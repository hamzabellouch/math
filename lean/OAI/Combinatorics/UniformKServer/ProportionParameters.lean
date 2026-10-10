import Mathlib
import OAI.Combinatorics.UniformKServer.AlphaTracker
import OAI.Combinatorics.UniformKServer.AlphaStability

namespace OAI

                                           
section

/-! Exact compact alpha update uniformly across unmarked, marked, and automatic
singleton stars. The fixed numerical envelopes are justified by the actual
held epoch geometry in EpochParameters; they are not competitive assumptions. -/
noncomputable section
namespace UniformKServer.ProportionParameters
open Finset
open scoped Classical
open UniformKServer.SimplexTracker UniformKServer.AlphaTracker
variable {ι : Type*} [Fintype ι]

inductive Kind (ι : Type*) where
  | regular
  | marked (o : ι) (u : ℝ)
  | singleton (o : ι)

structure Parameters (ι : Type*) where
  kind : Kind ι
  h : ι → ℝ
  ell : ℝ
  ct : ℝ
  C : ℝ

def eta (p : Parameters ι) (i : ι) : ℝ := p.ct*p.h i/p.ell

def valid (p : Parameters ι) : Prop :=
  0 < p.ell ∧ 0 < p.ct ∧ 1000 < p.C*p.ct ∧ (∀ i, eta p i ≤ 1) ∧
  match p.kind with
  | .regular => (∀ i, 1 ≤ p.h i) ∧ (∑ i, Real.exp (-p.h i)) ≤ 2
  | .marked o u => 0 < u ∧ u ≤ 1 ∧ p.h o=u ∧
      (∀ i, i ≠ o → 1 ≤ p.h i) ∧
      (∀ i, i ≠ o → (1/2)*Denominators.height u ≤ p.h i) ∧
      (∑ i ∈ univ.erase o, Real.exp (-p.h i)) ≤ 2*u
  | .singleton o => (∀ i, i=o) ∧ (∀ i, p.h i=0)

def component (p : Parameters ι) (B : ι → ℝ) (i : ι) : ℝ → ℝ :=
  match p.kind with
  | .regular => regularG p.h B p.ell p.ct p.C i
  | .marked o u => markedG o u p.h B p.ell p.ct p.C i
  | .singleton _ => fun _ => 0

def potential (p : Parameters ι) (B a : ι → ℝ) : ℝ := ∑ i, component p B i (a i)

theorem C_pos {p : Parameters ι} (hp : valid p) : 0 < p.C :=
  pos_of_mul_pos_left (by linarith [hp.2.2.1] : 0 < p.C*p.ct) hp.2.1.le

theorem h_nonneg {p : Parameters ι} (hp : valid p) (i : ι) : 0 ≤ p.h i := by
  rcases hp with ⟨_,_,_,_,hk⟩
  cases he : p.kind with
  | regular => simp only [he] at hk; linarith [hk.1 i]
  | marked o u =>
    simp only [he] at hk
    by_cases hi : i=o
    · rw [hi,hk.2.2.1]; exact hk.1.le
    · linarith [hk.2.2.2.1 i hi]
  | singleton o => simp only [he] at hk; rw [hk.2 i]

theorem eta_nonneg {p : Parameters ι} (hp : valid p) (i : ι) : 0 ≤ eta p i :=
  div_nonneg (mul_nonneg hp.2.1.le (h_nonneg hp i)) hp.1.le

theorem singleton_sum (o : ι) (ho : ∀ i, i=o) (f : ι → ℝ) (i : ι) :
    (∑ j, f j)=f i := by
  apply sum_eq_single i
  · intro j _ hji
    exact False.elim (hji ((ho j).trans (ho i).symm))
  · simp

theorem update {p : Parameters ι} (hp : valid p) (B a₀ : ι → ℝ)
    (hB : ∀ i, 0 ≤ B i) (ha₀ : simplex a₀) :
    ∃ a, simplex a ∧ (∀ i, (∑ j, B j)*a i ≤ (1+eta p i)*B i) ∧
      (∑ j, B j)*movement a a₀ ≤ potential p B a₀-potential p B a := by
  rcases hp with ⟨hl,hc,hC,hη,hk⟩
  cases he : p.kind with
  | regular =>
    simp only [he] at hk
    have hu := regular_update p.h B a₀ p.ell p.ct p.C 1 2 hB hk.1 hl hc
      (by norm_num) (by norm_num) hη (by linarith) hk.2 ha₀
    obtain ⟨a,ha,_,hf,hm⟩ := hu
    exact ⟨a,ha,hf,by simpa only [potential,component,he] using hm⟩
  | marked o u =>
    simp only [he] at hk
    have hu := marked_update o u (1/2) 2 p.h B a₀ p.ell p.ct p.C 1
      hk.1 hk.2.1 (by norm_num) (by norm_num) (by norm_num) hk.2.2.1
      hk.2.2.2.1 hk.2.2.2.2.1 hk.2.2.2.2.2 hB hl hc (by norm_num) hη
      (by norm_num; linarith) ha₀
    obtain ⟨a,ha,_,hf,hm⟩ := hu
    exact ⟨a,ha,hf,by simpa only [potential,component,he] using hm⟩
  | singleton o =>
    simp only [he] at hk
    refine ⟨a₀,ha₀,?_,?_⟩
    · intro i
      have ha : a₀ i=1 := (singleton_sum o hk.1 a₀ i).symm.trans ha₀.2
      rw [singleton_sum o hk.1 B i,ha]
      simp [eta,hk.2 i]
    · simp [movement,potential,component,he]

theorem primitive_zero (D : ℝ → ℝ) (base scale a : ℝ) :
    LogPrimitive.primitive D base scale 0 0 a=0 := by
  simp [LogPrimitive.primitive]

theorem component_zero (p : Parameters ι) (i : ι) (a : ℝ) :
    component p (fun _ => 0) i a=0 := by
  unfold component
  cases p.kind <;> simp [regularG,markedG,primitive_zero]

theorem potential_zero (p : Parameters ι) (a : ι → ℝ) : potential p (fun _ => 0) a=0 := by
  simp [potential,component_zero]

theorem component_mixed {p : Parameters ι} {o : ι} {u : ℝ} (he : p.kind=.marked o u)
    (B a : ι → ℝ) (i : ι) : component p B i (a i)=
      AlphaStability.mixedPrimitive o u p.h (eta p) B (p.C*p.ell) a i := by
  unfold component
  rw [he]
  dsimp only
  unfold markedG markedF AlphaStability.mixedPrimitive eta
  by_cases hi : i=o <;> simp only [hi,ite_true,ite_false]

/-- The same bound works on the entire old compact simplex, even when the
 filtered core input violates current coordinate feasibility. -/
theorem input_bound {p : Parameters ι} (hp : valid p) (B B' a : ι → ℝ)
    (ha : simplex a) :
    |potential p B a-potential p B' a| ≤
      15*(p.C*p.ell)*(∑ i, |B i-B' i|) := by
  have hC := C_pos hp
  have hscale : 0 ≤ p.C*p.ell := mul_nonneg hC.le hp.1.le
  have ha' : ∀ i, a i ∈ Set.Icc (0:ℝ) 1 :=
    fun i => ⟨ha.1 i,coordinate_le_one ha i⟩
  have hη := eta_nonneg hp
  have hη' := hp.2.2.2.1
  have hk := hp.2.2.2.2
  cases he : p.kind with
  | regular =>
    simp only [he] at hk
    have hb := AlphaStability.regular_input p.h (eta p) a B B' (p.C*p.ell) 1
      hk.1 ha' ha.2 hη hη'
    rw [abs_of_nonneg hscale] at hb
    change |(∑ i, regularG p.h B p.ell p.ct p.C i (a i))-
      (∑ i, regularG p.h B' p.ell p.ct p.C i (a i))| ≤ _ at hb
    have heq : potential p B a=∑ i, regularG p.h B p.ell p.ct p.C i (a i) := by simp [potential,component,he]
    have heq' : potential p B' a=∑ i, regularG p.h B' p.ell p.ct p.C i (a i) := by simp [potential,component,he]
    rw [heq,heq']
    refine hb.trans ?_
    have hn : 0 ≤ ∑ i, |B i-B' i| := sum_nonneg fun i _ => abs_nonneg _
    nlinarith
  | marked o u =>
    simp only [he] at hk
    have hb := AlphaStability.marked_input o p.h (eta p) a B B' (p.C*p.ell) 1 u
      hk.1 hk.2.1 hk.2.2.2.1 ha' ha.2 hη hη'
    rw [abs_of_nonneg hscale] at hb
    norm_num at hb
    simpa only [potential,component_mixed he,mul_comm (p.C*p.ell) 15] using hb
  | singleton o =>
    simp only [potential,component,he,sum_const_zero,sub_self,abs_zero]
    positivity

theorem potential_bound {p : Parameters ι} (hp : valid p) (B a : ι → ℝ)
    (hB : ∀ i, 0 ≤ B i) (ha : simplex a) :
    |potential p B a| ≤ 15*(p.C*p.ell)*(∑ i, B i) := by
  have h := input_bound hp B (fun _ => 0) a ha
  simpa only [potential_zero,sub_zero,abs_of_nonneg (hB _)] using h

end UniformKServer.ProportionParameters

end


end

end OAI
