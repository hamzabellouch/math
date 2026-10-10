import Mathlib
import OAI.Combinatorics.SharpRamsey.Reciprocal.ProdRectangleEvent

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset
open scoped Classical BigOperators NNReal
noncomputable section
variable {A B ι : Type*} [Fintype A] [Fintype B] [Fintype ι] [DecidableEq ι]
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

def rectangleBound (p : Law (ι→A×B)) (v : B→V) (w : A→Module.Dual K V) (M : ℝ) : Prop :=
  ∀ x,p.mass x≠0 → ∀ W : Submodule K V,
    ((univ.filter (fun i => x i∈orthogonalRectangle v w W)).card:ℝ)≤M

def tupleFlags (p : Law (ι→A×B)) (v : B→V) (w : A→Module.Dual K V) : Prop :=
  ∀ x,p.mass x≠0 → ∀ i,w (x i).1 (v (x i).2)=0

def rankCollision (p : Law (ι→A×B)) (v : B→V) (w : A→Module.Dual K V)
    (ρ : ℝ) (r s : ℕ) (i j : ι) (x : ι→A×B) : Prop :=
  coreCollision (p.marginal i) (p.marginal j) v w ρ
    (fun a => r≤Module.finrank K (firstCore (K:=K) (p.marginal i) v ρ a))
    (fun y => s≤Module.finrank K (secondCore (p.marginal j) w ρ y)) (x i,x j)

def directedCollision (p : Law (ι→A×B)) (v : B→V) (w : A→Module.Dual K V)
    (ρ : ℝ) (r s : ℕ) (i j : ι) : ℝ≥0 :=
  ⟨p.event (univ.filter (rankCollision p v w ρ r s i j)),p.event_nonneg _⟩

def reciprocalCharges (p : Law (ι→A×B)) (v : B→V) (w : A→Module.Dual K V)
    (ρ : ℝ) (r s : ℕ) (i j : ι) : ℝ≥0 :=
  directedCollision p v w ρ r s i j+directedCollision p v w ρ r s j i

omit [FiniteDimensional K V] in
lemma marginal_flag (p : Law (ι→A×B)) (v : B→V) (w : A→Module.Dual K V)
    (hf : tupleFlags p v w) (i : ι) (ab : A×B) (ha : (p.marginal i).mass ab≠0) :
    w ab.1 (v ab.2)=0 := by
  obtain ⟨x,hx,rfl⟩ := p.map_support (fun x => x i) ab ha
  exact hf x hx i

lemma rankCollision_rectangle (p : Law (ι→A×B)) (v : B→V) (w : A→Module.Dual K V)
    {ρ : ℝ} (hρ : 0≤ρ) {r s : ℕ} (hsum : Module.finrank K V=r+s)
    (hflag : tupleFlags p v w) (x : ι→A×B) (hx : p.mass x≠0) (i j : ι)
    (hc : rankCollision p v w ρ r s i j x) :
    x j∈orthogonalRectangle v w (firstCore (K:=K) (p.marginal i) v ρ (x i).1) := by
  have hpi : (p.marginal i).mass (x i)≠0 :=
    (lt_of_lt_of_le (lt_of_le_of_ne (p.nonneg x) (Ne.symm hx)) (p.le_map _ x)).ne'
  have hpj : (p.marginal j).mass (x j)≠0 :=
    (lt_of_lt_of_le (lt_of_le_of_ne (p.nonneg x) (Ne.symm hx)) (p.le_map _ x)).ne'
  exact (coreCollision_rectangle _ _ v w hρ _ _
    (marginal_flag p v w hflag i) (marginal_flag p v w hflag j) hsum
    (fun _ h => h) (fun _ h => h) (x i) (x j) hpi hpj hc).2

theorem directedCollision_sum (p : Law (ι→A×B)) (v : B→V) (w : A→Module.Dual K V)
    {ρ M : ℝ} (hρ : 0≤ρ) {r s : ℕ} (hsum : Module.finrank K V=r+s)
    (hflag : tupleFlags p v w) (hocc : rectangleBound p v w M) :
    ∑ i,∑ j,(directedCollision p v w ρ r s i j:ℝ)≤Fintype.card ι*M := by
  let C := rankCollision p v w ρ r s
  have hpoint (x : ι→A×B) (hx : p.mass x≠0) (i : ι) :
      ∑ j,(if C i j x then (1:ℝ) else 0)≤M := by
    have hs : univ.filter (fun j => C i j x)⊆
        univ.filter (fun j => x j∈orthogonalRectangle v w
          (firstCore (K:=K) (p.marginal i) v ρ (x i).1)) := by
      intro j hj
      exact mem_filter.mpr ⟨mem_univ _,rankCollision_rectangle p v w hρ hsum hflag x hx i j (mem_filter.mp hj).2⟩
    have hc := (Nat.cast_le.mpr (card_le_card hs) :
      ((univ.filter (fun j => C i j x)).card:ℝ)≤_)
    simpa only [sum_boole] using hc.trans (hocc x hx _)
  have he (i j : ι) : (directedCollision p v w ρ r s i j:ℝ)=
      ∑ x,p.mass x*(if C i j x then (1:ℝ) else 0) := by
    simp only [directedCollision,Law.event,sum_filter,mul_ite,mul_one,mul_zero]
    rfl
  simp_rw [he]
  have hswap : (∑ i,∑ j,∑ x,p.mass x*(if C i j x then (1:ℝ) else 0))=
      ∑ x,p.mass x*(∑ i,∑ j,(if C i j x then (1:ℝ) else 0)) := by
    conv_lhs => arg 2; ext i; rw [sum_comm]
    rw [sum_comm]
    simp_rw [mul_sum]
  rw [hswap]
  calc
    _ ≤ ∑ x,p.mass x*(Fintype.card ι*M) := by
      apply sum_le_sum
      intro x _
      by_cases hx : p.mass x=0
      · simp [hx]
      apply mul_le_mul_of_nonneg_left _ (p.nonneg x)
      exact (sum_le_sum (fun i _ => hpoint x hx i)).trans_eq (by simp)
    _ = _ := by rw [←sum_mul,p.total,one_mul]

theorem reciprocalCharges_sum (p : Law (ι→A×B)) (v : B→V) (w : A→Module.Dual K V)
    {ρ M : ℝ} (hρ : 0≤ρ) {r s : ℕ} (hsum : Module.finrank K V=r+s)
    (hflag : tupleFlags p v w) (hocc : rectangleBound p v w M) :
    ∑ i,∑ j,(reciprocalCharges p v w ρ r s i j:ℝ)≤2*Fintype.card ι*M := by
  simp only [reciprocalCharges,NNReal.coe_add,sum_add_distrib]
  rw [sum_comm (f:=fun i j => (directedCollision p v w ρ r s j i:ℝ))]
  linarith only [directedCollision_sum p v w hρ hsum hflag hocc]

end
end SharpLogRamsey.Selection

end

end OAI
