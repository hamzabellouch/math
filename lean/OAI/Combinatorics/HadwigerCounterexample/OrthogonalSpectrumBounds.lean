import OAI.Combinatorics.HadwigerCounterexample.ReindexedFourierSupport

namespace OAI

/-! # Orthogonal Spectrum Bounds -/

noncomputable section
namespace HadwigerCounterexample
open Finset Matrix Module LinearMap Submodule Function
open scoped BigOperators
variable {p : Shape} {n : ℕ}

def fieldRad (S : Space (Vec (Fin n))) : Finset (Vec (Fin n)) :=
  open Classical in univ.filter (fun i => i∈S)
@[simp] theorem mem_fieldRad (S : Space (Vec (Fin n))) (i) :
    i∈fieldRad S↔i∈S := by simp [fieldRad]
theorem card_fieldRad (S : Space (Vec (Fin n))) : ((fieldRad S).card:ℝ)=bp (dim S) := by
  classical
  rw [←card_space]
  let e : S≃ (↑(fieldRad S) : Type) := {
    toFun x := ⟨x.val, by simp⟩
    invFun x := ⟨x.val,(mem_fieldRad ..).mp x.property⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  exact_mod_cast (Fintype.card_coe (fieldRad S)).symm.trans (Fintype.card_congr e).symm

def zsafe (p : Shape) (w f : Wgt (Knobs p.g n)) (S : Space (Vec (Fin n))) :=
  ∀ (g : Wgt (Knobs p.g n)) (t : Finset (Vec (Fin n))),
    (∀ i∈t,i∉S) → avg w (fun i => f i * zim p g t i)=0
def zsumPeak (p : Shape) (w f : Wgt (Knobs p.g n)) (P : Knobs p.g n → Prop) :=
  avg w (fun i => ind (P i)*f i)

set_option maxHeartbeats 800000 in
theorem clear_band (p : Shape) (w f : Wgt (Knobs p.g n)) (P : Knobs p.g n→Prop)
    (hw : IsLaw w) (hf : ∀ i, |f i|≤1) (h : flowZ p w)
    (b g : ℝ) (hb : 0≤b) (hq : g*pr w P≤ |zsumPeak p w f P|)
    (S T : Space (Vec (Fin n))) (s : ℕ) (hS : dim (S⊓T : Space (Vec (Fin n))) ≤ s)
    (hh : ∀ x i, |zchar p f i x|≤b ∧ (i∉T → zchar p f i x=0)) :
    ∃ (t : Finset (Vec (Fin n))) (a : ℝ), |a|=1 ∧
      (∀ i∈ t,i∉S ∧ i∈T) ∧
      let F i := a * zim p f t i
      (g-b*bp s)*pr w P ≤ zsumPeak p w F P ∧ avg w (fun i => F i ^ 2)≤1 := by
  classical
  let A := fieldRad T
  let B := fieldRad (S⊓T); let D := A\B
  have hB : B⊆A := fun i hi => (mem_fieldRad T i).mpr (((mem_fieldRad (S⊓T) i).mp hi).2)
  have he x : f x=zim p f D x+zim p f B x := by
    unfold zim D
    rw [Finset.sum_sdiff hB]
    change f x=∑ i∈A,_
    exact (z_atlas p f x).symm.trans (Finset.sum_subset (subset_univ A)
      (fun i _ hi=> (hh x i).2 (fun h => hi ((mem_fieldRad ..).mpr h)))).symm
  let V x := zsumPeak p w x P
  have hm (x) :
      |zim p f B x|≤b*bp s := by
    have hx : ((B.card:ℝ))≤bp s := le_trans (le_of_eq (card_fieldRad (S⊓T)))
      (bp_le (by exact_mod_cast hS))
    refine (abs_sum_le_sum_abs ..).trans ((Finset.sum_le_sum
      (s:=B) (fun i _ => (hh x i).1)).trans ?_)
    simp only [Finset.sum_const,nsmul_eq_mul,mul_comm b]
    exact mul_le_mul_of_nonneg_right hx hb
  have hz :
      |V (zim p f B)| ≤ b*bp s*pr w P := by
    apply (abs_avg_le hw.nz).trans
    have he (x : Knobs p.g n) :
        |ind (P x)*zim p f B x|≤ (b*bp s)*ind (P x) := by
      rw [abs_mul,abs_of_nonneg (ind_nonneg _),mul_comm (b*bp s)]
      exact mul_le_mul_of_nonneg_left (hm x) (ind_nonneg _)
    exact (avg_mono hw.nz he).trans_eq (avg_mul' ..)
  have h2 :
      |V f|≤|V (zim p f D)| + |V (zim p f B)| := by
    have ht :
        V f= V (zim p f D)+V (zim p f B) := by
      unfold V zsumPeak; rw [← avg_add]
      apply avg_congr; intro x _
      conv_lhs => rhs; rw [he x]
      rw [mul_add]
    rw [ht]; exact abs_add_le ..
  have hb :
      (g-b*bp s)*pr w P≤|V (zim p f D)| := by linarith only [hq,h2,hz]
  let a : ℝ := if 0≤ V (zim p f D) then 1 else -1
  have ha : |a|=1 := by unfold a; split <;> norm_num
  have hi :
      V (fun i=>a*zim p f D i) = |V (zim p f D)| := by
    have he (i : Knobs p.g n) : ind (P i)*(a*zim p f D i)=a*(ind (P i)*zim p f D i) := by ring
    have hh : V (fun i=>a*zim p f D i)=a*V (zim p f D) := by
      unfold V zsumPeak; simp_rw [he,avg_mul']
    rw [hh]; unfold a
    split
    next h => rw [one_mul,abs_of_nonneg h]
    next h => simp only [neg_mul,one_mul,abs_of_neg (lt_of_not_ge h)]
  refine ⟨D,a,ha,fun i hit => ?_,hb.trans_eq hi.symm,?_⟩
  · obtain ⟨h0,h1⟩ := mem_sdiff.mp hit
    obtain h2 := (mem_fieldRad ..).mp h0
    exact ⟨fun h => h1 ((mem_fieldRad (S⊓T) _).mpr ⟨h,h2⟩),h2⟩
  have ha' : a^2=1 := by rw [←sq_abs,ha]; norm_num
  simp_rw [mul_pow,ha',one_mul]
  exact (zsplit_cost p f w h hw.nz D).trans (hw.avg_le (fun i=>by
    have h := hf i
    nlinarith only [sq_abs (f i),abs_nonneg (f i),h]))
end HadwigerCounterexample

end

end OAI
