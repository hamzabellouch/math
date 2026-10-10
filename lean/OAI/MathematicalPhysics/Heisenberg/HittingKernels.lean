import OAI.MathematicalPhysics.Heisenberg.LayerExposure

namespace OAI

noncomputable section
open scoped Classical
open Matrix
open scoped Classical
open Matrix
open scoped Classical
open Matrix
open scoped Classical
open scoped BigOperators Classical
open scoped Classical

namespace Heisenberg.Hitting
open Filter
variable {V : Type*} [Fintype V]

def affineIter (A : Matrix V V ℝ) (b : V → ℝ) : ℕ → V → ℝ
  | 0 => 0
  | n+1 => b + A *ᵥ affineIter A b n

omit [Fintype V] in
lemma mulVec_mono {W : Type*} [Fintype W] {A : Matrix V W ℝ} (hA : ∀ i j,0 ≤ A i j)
    {f g : W → ℝ} (h : f ≤ g) : A *ᵥ f ≤ A *ᵥ g := by
  intro i
  exact Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (h j) (hA i j))

lemma affineIter_mono {A : Matrix V V ℝ} {b : V → ℝ}
    (hA : ∀ i j,0 ≤ A i j) (hb : 0 ≤ b) : Monotone (affineIter A b) := by
  apply monotone_nat_of_le_succ
  intro n
  induction n with
  | zero => simpa [affineIter] using hb
  | succ n ih => exact add_le_add le_rfl (mulVec_mono hA ih)

lemma affineIter_nonneg {A : Matrix V V ℝ} {b : V → ℝ}
    (hA : ∀ i j,0 ≤ A i j) (hb : 0 ≤ b) (n : ℕ) : 0 ≤ affineIter A b n :=
  affineIter_mono hA hb (Nat.zero_le n)

lemma affineIter_super {A : Matrix V V ℝ} {b g : V → ℝ}
    (hA : ∀ i j,0 ≤ A i j) (hg : 0 ≤ g) (hs : b + A *ᵥ g ≤ g) (n : ℕ) :
    affineIter A b n ≤ g := by
  induction n with
  | zero => exact hg
  | succ n ih => exact (add_le_add le_rfl (mulVec_mono hA ih)).trans hs

def affineHit (A : Matrix V V ℝ) (b : V → ℝ) (i : V) : ℝ := ⨆ n, affineIter A b n i

lemma affineIter_bdd {A : Matrix V V ℝ} {b g : V → ℝ}
    (hA : ∀ i j,0 ≤ A i j) (hg : 0 ≤ g) (hs : b + A *ᵥ g ≤ g) (i : V) :
    BddAbove (Set.range (fun n => affineIter A b n i)) :=
  ⟨g i,fun _ ⟨n,hn⟩ => hn ▸ affineIter_super hA hg hs n i⟩

lemma affineIter_tendsto {A : Matrix V V ℝ} {b g : V → ℝ}
    (hA : ∀ i j,0 ≤ A i j) (hb : 0 ≤ b)
    (hg : 0 ≤ g) (hs : b + A *ᵥ g ≤ g) (i : V) :
    Tendsto (fun n => affineIter A b n i) atTop (nhds (affineHit A b i)) :=
  tendsto_atTop_ciSup (fun _ _ h => affineIter_mono hA hb h i) (affineIter_bdd hA hg hs i)

lemma affineHit_fixed {A : Matrix V V ℝ} {b g : V → ℝ}
    (hA : ∀ i j,0 ≤ A i j) (hb : 0 ≤ b)
    (hg : 0 ≤ g) (hs : b + A *ᵥ g ≤ g) : b + A *ᵥ affineHit A b = affineHit A b := by
  funext i
  have h₁ : Tendsto (fun n => b i + ∑ j,A i j * affineIter A b n j) atTop
      (nhds (b i + ∑ j,A i j * affineHit A b j)) :=
    tendsto_const_nhds.add (tendsto_finsetSum _
      (fun j _ => tendsto_const_nhds.mul (affineIter_tendsto hA hb hg hs j)))
  have h₂ := (affineIter_tendsto hA hb hg hs i).comp (tendsto_add_atTop_nat 1)
  exact tendsto_nhds_unique h₁ h₂

lemma affineHit_super {A : Matrix V V ℝ} {b g : V → ℝ}
    (hA : ∀ i j,0 ≤ A i j) (hg : 0 ≤ g) (hs : b + A *ᵥ g ≤ g) :
    affineHit A b ≤ g := fun i => ciSup_le (fun n => affineIter_super hA hg hs n i)

lemma affineHit_nonneg {A : Matrix V V ℝ} {b g : V → ℝ}
    (hA : ∀ i j,0 ≤ A i j) (hg : 0 ≤ g) (hs : b + A *ᵥ g ≤ g) :
    0 ≤ affineHit A b := by
  intro i
  exact le_ciSup (affineIter_bdd hA hg hs i) 0

variable [DecidableEq V]

theorem affineHit_inverse {A : Matrix V V ℝ} {b g : V → ℝ}
    (hA : ∀ i j,0 ≤ A i j) (hb : 0 ≤ b)
    (hg : 0 ≤ g) (hs : b + A *ᵥ g ≤ g) (hd : (1-A).det ≠ 0) :
    affineHit A b = (1-A)⁻¹ *ᵥ b := by
  have he : (1-A) *ᵥ affineHit A b = b := by
    rw [Matrix.sub_mulVec,Matrix.one_mulVec]
    exact sub_eq_iff_eq_add.mpr (affineHit_fixed hA hb hg hs).symm
  calc
    affineHit A b = (1-A)⁻¹ *ᵥ ((1-A) *ᵥ affineHit A b) := by
      rw [Matrix.mulVec_mulVec,Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hd),Matrix.one_mulVec]
    _ = (1-A)⁻¹ *ᵥ b := by rw [he]

end Heisenberg.Hitting
namespace Heisenberg.Exposure

section
variable {J Q : Type*} [Fintype J] [Fintype Q] [DecidableEq J] [DecidableEq Q]
omit [DecidableEq J] [DecidableEq Q] in
lemma backward_split_left (K : Matrix (J ⊕ Q) (J ⊕ Q) ℝ) (g : (J ⊕ Q) → ℝ) :
    (K.transpose *ᵥ g) ∘ Sum.inl =
      K.toBlocks₁₁.transpose *ᵥ (g ∘ Sum.inl) + K.toBlocks₂₁.transpose *ᵥ (g ∘ Sum.inr) := by
  ext i
  simp [Matrix.mulVec, dotProduct,Fintype.sum_sum_type,Matrix.toBlocks₁₁,Matrix.toBlocks₂₁]

omit [DecidableEq J] [DecidableEq Q] in
lemma backward_split_right (K : Matrix (J ⊕ Q) (J ⊕ Q) ℝ) (g : (J ⊕ Q) → ℝ) :
    (K.transpose *ᵥ g) ∘ Sum.inr =
      K.toBlocks₁₂.transpose *ᵥ (g ∘ Sum.inl) + K.toBlocks₂₂.transpose *ᵥ (g ∘ Sum.inr) := by
  ext i
  simp [Matrix.mulVec, dotProduct,Fintype.sum_sum_type,Matrix.toBlocks₁₂,Matrix.toBlocks₂₂]

omit [DecidableEq J] in
lemma resolvent_backward (K : Matrix (J ⊕ Q) (J ⊕ Q) ℝ) (b : J → ℝ) :
    (hittingResolvent ℝ K).transpose *ᵥ b =
      K.toBlocks₁₁.transpose *ᵥ b + K.toBlocks₂₁.transpose *ᵥ
        ((1-K.toBlocks₂₂.transpose)⁻¹ *ᵥ (K.toBlocks₁₂.transpose *ᵥ b)) := by
  simp only [hittingResolvent,Matrix.transpose_add,Matrix.transpose_mul,
    Matrix.add_mulVec,Matrix.mulVec_mulVec,Matrix.transpose_nonsing_inv,
    Matrix.transpose_sub,Matrix.transpose_one]

omit [DecidableEq J] in
theorem resolvent_le_supersolution (K : Matrix (J ⊕ Q) (J ⊕ Q) ℝ)
    (hK : ∀ i j,0 ≤ K i j) (hd : (1-K.toBlocks₂₂).det ≠ 0)
    (b : J → ℝ) (hb : 0 ≤ b) (g : (J ⊕ Q) → ℝ) (hg : 0 ≤ g)
    (hP : b ≤ g ∘ Sum.inl)
    (hQ : (K.transpose *ᵥ g) ∘ Sum.inr ≤ g ∘ Sum.inr) :
    (hittingResolvent ℝ K).transpose *ᵥ b ≤ (K.transpose *ᵥ g) ∘ Sum.inl := by
  let A := K.toBlocks₂₂.transpose
  let c := K.toBlocks₁₂.transpose *ᵥ b
  have hA : ∀ i j,0 ≤ A i j := fun i j => hK (Sum.inr j) (Sum.inr i)
  have hc : 0 ≤ c := by
    intro i
    exact Finset.sum_nonneg (fun j _ => mul_nonneg (hK (Sum.inl j) (Sum.inr i)) (hb j))
  have hs : c + A *ᵥ (g ∘ Sum.inr) ≤ g ∘ Sum.inr := by
    apply le_trans (add_le_add (Hitting.mulVec_mono
      (A := K.toBlocks₁₂.transpose) (fun i j => hK (Sum.inl j) (Sum.inr i)) hP) le_rfl)
    exact (backward_split_right K g) ▸ hQ
  have hdA : (1-A).det ≠ 0 := by
    have he : 1-A = (1-K.toBlocks₂₂).transpose := by
      rw [Matrix.transpose_sub,Matrix.transpose_one]
    rw [he,Matrix.det_transpose]
    exact hd
  have hv := Hitting.affineHit_super hA (fun i => hg (Sum.inr i)) hs
  rw [Hitting.affineHit_inverse hA hc (fun i => hg (Sum.inr i)) hs hdA] at hv
  rw [resolvent_backward,backward_split_left]
  apply add_le_add
  · exact Hitting.mulVec_mono (fun i j => hK (Sum.inl j) (Sum.inl i)) hP
  · exact Hitting.mulVec_mono (fun i j => hK (Sum.inr j) (Sum.inl i)) hv

end

section
variable {J Q Ω : Type*} [Fintype J] [Fintype Q] [Fintype Ω]
  [DecidableEq J] [DecidableEq Q]

omit [Fintype J] [Fintype Q] in
lemma columnPerm_nonneg (π : Equiv.Perm (J ⊕ Q)) (i j : J ⊕ Q) :
    0 ≤ columnPerm ℝ π i j := by
  change 0 ≤ if i ∈ (Equiv.toPEquiv π) j then (1:ℝ) else 0
  split_ifs <;> norm_num

omit [DecidableEq Q] in
lemma nextPinMatrix_backward (π : Equiv.Perm (J ⊕ Q)) (h : AllHit π) (b : J → ℝ) :
    (nextPinMatrix ℝ π h).transpose *ᵥ b = b ∘ nextPin π h := by
  ext j
  simp [Matrix.mulVec,dotProduct,nextPinMatrix]

theorem conditional_return_le (μ : Ω → ℝ) (hμ : ∀ ω,0 ≤ μ ω)
    (π : Ω → Equiv.Perm (J ⊕ Q))
    (h : DeterminantLaw μ (fun ω => columnPerm ℝ (π ω)))
    (hz : hitWeight μ π ≠ 0) (T : Finset J)
    (g : (J ⊕ Q) → ℝ) (hg : 0 ≤ g)
    (hT : ∀ j ∈ T,1 ≤ g (Sum.inl j))
    (hQ : (((∑ ω,μ ω • columnPerm ℝ (π ω)).transpose *ᵥ g) ∘ Sum.inr) ≤ g ∘ Sum.inr) :
    (∑ ω,if hw : AllHit (π ω) then
      (μ ω / hitWeight μ π)*(∑ j ∈ T,if nextPin (π ω) hw j ∈ T then (1:ℝ) else 0) else 0) ≤
    ∑ j ∈ T,((∑ ω,μ ω • columnPerm ℝ (π ω)).transpose *ᵥ g) (Sum.inl j) := by
  let b : J → ℝ := fun j => if j ∈ T then 1 else 0
  let K : Matrix (J ⊕ Q) (J ⊕ Q) ℝ := ∑ ω,μ ω • columnPerm ℝ (π ω)
  have hK : ∀ i j,0 ≤ K i j := by
    intro i j
    simp only [K,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul]
    exact Finset.sum_nonneg (fun ω _ => mul_nonneg (hμ ω) (columnPerm_nonneg (π ω) i j))
  have hd : (1-K.toBlocks₂₂).det ≠ 0 := by rw [←allHit_determinant μ π h]; exact hz
  have hb : 0 ≤ b := by intro j; dsimp [b]; split_ifs <;> norm_num
  have hP : b ≤ g ∘ Sum.inl := by
    intro j
    dsimp [b]
    split_ifs with hj
    · exact hT j hj
    · exact hg _
  have hs := resolvent_le_supersolution K hK hd b hb g hg hP hQ
  have he := conditional_nextPin_first_moment μ π h hz
  have hv : (hittingResolvent ℝ K).transpose *ᵥ b =
      ∑ ω,if hw : AllHit (π ω) then
        (μ ω / hitWeight μ π) • (b ∘ nextPin (π ω) hw) else 0 := by
    rw [←he,Matrix.transpose_sum,Matrix.sum_mulVec]
    apply Finset.sum_congr rfl
    intro ω _
    split_ifs with hw
    · rw [Matrix.transpose_smul,Matrix.smul_mulVec,nextPinMatrix_backward]
    · simp
  have heq : (∑ ω,if hw : AllHit (π ω) then
      (μ ω / hitWeight μ π)*(∑ j ∈ T,if nextPin (π ω) hw j ∈ T then (1:ℝ) else 0) else 0) =
      ∑ j ∈ T,((hittingResolvent ℝ K).transpose *ᵥ b) j := by
    rw [hv]
    simp only [Finset.sum_apply,Finset.sum_comm (s:=T)]
    apply Finset.sum_congr rfl
    intro ω _
    by_cases hw : AllHit (π ω)
    · simp only [dite_eq_left hw,Pi.smul_apply,smul_eq_mul,Function.comp_apply,b]
      rw [Finset.mul_sum]
    · simp [hw]
  rw [heq]
  exact Finset.sum_le_sum (fun j _ => hs j)

end

open Matrix
variable {V Ω : Type*} [Fintype V] [Fintype Ω] [DecidableEq V]

lemma mean_perm_backward (μ : Ω → ℝ) (π : Ω → Equiv.Perm V) (g : V → ℝ) (x : V) :
    ((∑ c, μ c • (π c).permMatrix ℝ) *ᵥ g) x = ∑ c,μ c*g (π c x) := by
  rw [Matrix.sum_mulVec]
  simp only [Finset.sum_apply,Matrix.smul_mulVec,Matrix.permMatrix_mulVec,
    Pi.smul_apply,smul_eq_mul,Function.comp_apply]

lemma split_mean_backward (μ : Ω → ℝ) (σ : Ω → Equiv.Perm V) (A P : Set V)
    (hA : ∀ c x,σ c x ∉ A ↔ x ∉ A) (g : V → ℝ)
    (x : {x : {z : V // z ∉ A} // x.val ∈ P} ⊕
      {x : {z : V // z ∉ A} // x.val ∉ P}) :
    let e := Equiv.sumCompl (fun x : {z : V // z ∉ A} => x.val ∈ P)
    ((∑ c,μ c • columnPerm ℝ (splitHolePerm (σ c) A P (hA c))).transpose *ᵥ
      (fun z => g (e z).val)) x =
        ((∑ c,μ c • (σ c).permMatrix ℝ) *ᵥ g) (e x).val := by
  dsimp only
  simp only [columnPerm,Matrix.transpose_sum,Matrix.transpose_smul,Matrix.transpose_transpose]
  rw [mean_perm_backward,mean_perm_backward]
  apply Finset.sum_congr rfl
  intro c _
  congr 1
  simp [splitHolePerm,Equiv.permCongr_apply]

theorem split_conditional_return_le (μ : Ω → ℝ) (hμ : ∀ c,0 ≤ μ c)
    (σ : Ω → Equiv.Perm V) (A P : Set V)
    (hA : ∀ c x,σ c x ∉ A ↔ x ∉ A)
    (hd : DeterminantLaw μ (fun c => (σ c).permMatrix ℝ |>.transpose))
    (hz : hitWeight μ (fun c => splitHolePerm (σ c) A P (hA c)) ≠ 0)
    (T : Finset {x : {z : V // z ∉ A} // x.val ∈ P})
    (g : V → ℝ) (hg : 0 ≤ g) (hT : ∀ j ∈ T,1 ≤ g j.val.val)
    (hQ : ∀ x,x ∉ A → x ∉ P → ((∑ c,μ c • (σ c).permMatrix ℝ) *ᵥ g) x ≤ g x) :
    (∑ c,if hw : AllHit (splitHolePerm (σ c) A P (hA c)) then
      (μ c / hitWeight μ (fun c => splitHolePerm (σ c) A P (hA c))) *
        (∑ j ∈ T,if nextPin (splitHolePerm (σ c) A P (hA c)) hw j ∈ T then (1:ℝ) else 0) else 0) ≤
      ∑ j ∈ T,((∑ c,μ c • (σ c).permMatrix ℝ) *ᵥ g) j.val.val := by
  let e := Equiv.sumCompl (fun x : {z : V // z ∉ A} => x.val ∈ P)
  let π := fun c => splitHolePerm (σ c) A P (hA c)
  have hh := LayeredExchange.determinantLaw_holes (μ:=μ) (π:=σ) hd (fun z => z ∉ A) hA
  have hh' := LayeredExchange.determinantLaw_reindexed hh e
  have he : DeterminantLaw μ (fun c => columnPerm ℝ (π c)) := hh'
  have hg' : 0 ≤ (fun z => g (e z).val) := fun _ => hg _
  have hT' : ∀ j ∈ T,1 ≤ g (e (Sum.inl j)).val := hT
  have hQ' : (((∑ c,μ c • columnPerm ℝ (π c)).transpose *ᵥ
      (fun z => g (e z).val)) ∘ Sum.inr) ≤ (fun z => g (e z).val) ∘ Sum.inr := by
    intro x
    change ((∑ c,μ c • columnPerm ℝ (splitHolePerm (σ c) A P (hA c))).transpose *ᵥ
      (fun z => g (e z).val)) (Sum.inr x) ≤ g x.val.val
    rw [split_mean_backward]
    exact hQ x.val.val x.val.property x.property
  have h := conditional_return_le μ hμ π he hz T (fun z => g (e z).val) hg' hT' hQ'
  convert h using 1
  apply Finset.sum_congr rfl
  intro j _
  exact (split_mean_backward μ σ A P hA g (Sum.inl j)).symm

end Heisenberg.Exposure
end

end OAI
