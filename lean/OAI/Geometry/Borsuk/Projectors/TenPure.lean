import Mathlib
import OAI.Geometry.Borsuk.Support.SupportIncidence

namespace OAI

open Set MeasureTheory
namespace BorsukNine
open scoped RealInnerProductSpace
section TenPure
lemma Admissible.face_extends_four {f : Vector4 → Fin 10 → ℝ} (hf : Admissible f)
    {U : Finset (Fin 10)} (hU : SupportFace f U) :
    ∃ I : Finset (Fin 10), I.card = 4 ∧ SupportFace f I ∧ U ⊆ I := by
  obtain ⟨w,hw,hUw⟩ := hU
  obtain ⟨u,hu,hwu,huc⟩ := hf.support_extends_four hw
  exact ⟨positiveSupport f u,huc,⟨u,hu,Finset.Subset.refl _⟩,hUw.trans hwu⟩
lemma Admissible.tetra_no_free_triangle {f : Vector4 → Fin 10 → ℝ} (hf : Admissible f)
    {I U : Finset (Fin 10)} (hIc : I.card = 4) (hIf : SupportFace f I)
    (hUI : U ⊆ I) (hUc : U.card = 3) :
    ∃ I' : Finset (Fin 10), I'.card = 4 ∧ SupportFace f I' ∧ U ⊆ I' ∧ I' ≠ I := by
  classical
  obtain ⟨w,hw,hIw⟩ := hIf
  have hmax (u : Vector4) (hu : ‖u‖ = 1) (hIu : I ⊆ positiveSupport f u) : positiveSupport f u = I :=
    (Finset.eq_of_subset_of_card_le hIu (by rw [hIc]; exact hf.support_card_four_le hu)).symm
  have hcomp : (Iᶜ : Finset (Fin 10)).Nonempty := by
    apply Finset.card_pos.mp
    rw [Finset.card_compl,Fintype.card_fin,hIc]
    decide
  let : Nonempty ↥(Iᶜ : Finset (Fin 10)) := hcomp.to_subtype
  obtain ⟨u,hu,hUu,hnu⟩ := hf.no_free_ridge (k := 3) (by decide) (by decide) (by decide) hIc hUI hUc hmax hw
    (fun i hi => (mem_positiveSupport f w i).mp (hIw hi))
  obtain ⟨I',hI'c,hI'f,hI'u⟩ := hf.face_extends_four (⟨u,hu,Finset.Subset.refl _⟩ : SupportFace f (positiveSupport f u))
  exact ⟨I',hI'c,hI'f,hUu.trans hI'u,fun he => hnu (he ▸ hI'u)⟩
end TenPure
end BorsukNine

namespace BorsukNine
open Set SimplicialChains
open scoped RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
section TwoLabels
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {ι : Type*} [Fintype ι] [DecidableEq ι]
lemma Admissible.sum_two_labels {f : V → ι → ℝ} (hf : Admissible f)
    {u : V} (hu : ‖u‖ = 1) {i j : ι} (hij : i ≠ j)
    (hzero : ∀ l, l ≠ i → l ≠ j → f u l = 0) : f u i + f u j = 1 := by
  have hsum : ∑ l, f u l = ∑ l ∈ ({i,j} : Finset ι), f u l :=
    (Finset.sum_subset (Finset.subset_univ _) (fun l _ hl => hzero l (by aesop) (by aesop))).symm
  simpa only [Finset.sum_pair hij] using hsum.symm.trans (hf.sum_one u hu)

lemma Admissible.two_labels_meet {f : V → ι → ℝ} (hf : Admissible f)
    (W : Submodule ℝ V) {i j : ι} (hij : i ≠ j)
    (hzero : ∀ u ∈ W, ‖u‖ = 1 → ∀ l, l ≠ i → l ≠ j → f u l = 0)
    {u v : V} (huW : u ∈ W) (hu : ‖u‖ = 1) (hui : 0 < f u i)
    (hvW : v ∈ W) (hv : ‖v‖ = 1) (hvj : 0 < f v j) :
    ∃ w : V, ‖w‖ = 1 ∧ 0 < f w i ∧ 0 < f w j := by
  classical
  by_contra hn
  have hnot (w : V) (hw : ‖w‖ = 1) : ¬ (0 < f w i ∧ 0 < f w j) := fun hh => hn ⟨w,hw,hh⟩
  have hui' : f u i = 1 := by
    have hj0 : f u j = 0 := le_antisymm (not_lt.mp (fun hp => hnot u hu ⟨hui,hp⟩)) (hf.nonneg u hu j)
    have hh := hf.sum_two_labels hu hij (hzero u huW hu)
    linarith
  have hvi : f v i = 0 := le_antisymm (not_lt.mp (fun hp => hnot v hv ⟨hp,hvj⟩)) (hf.nonneg v hv i)
  obtain ⟨v',hv'W,hv',hv'i,hinner⟩ : ∃ v' : V, v' ∈ W ∧ ‖v'‖ = 1 ∧ f v' i = 0 ∧ 0 ≤ ⟪u,v'⟫ := by
    by_cases hi : 0 ≤ ⟪u,v⟫
    · exact ⟨v,hvW,hv,hvi,hi⟩
    · exact ⟨-v,W.neg_mem hvW,by simpa using hv,by simpa only [hf.antipodal] using hvi,by simp only [inner_neg_right]; linarith⟩
  let p : ℝ → V := fun t => (1-t) • u + t • v'
  have hp : Continuous p := ((continuous_const.sub continuous_id).smul continuous_const).add (continuous_id.smul continuous_const)
  have hpW (t : ℝ) : p t ∈ W := W.add_mem (W.smul_mem _ huW) (W.smul_mem _ hv'W)
  have hpz (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : p t ≠ 0 := by
    intro hz
    have hi := congrArg (fun x : V => ⟪u,x⟫) hz
    have hi' : (1-t)+t*⟪u,v'⟫ = 0 := by
      simpa only [p,inner_add_right,inner_smul_right,real_inner_self_eq_norm_sq,hu,one_pow,mul_one,inner_zero_right] using hi
    have ht1 : t = 1 := by nlinarith [ht.2,mul_nonneg ht.1 hinner]
    have hv0 : v' = 0 := by simpa only [p,ht1,sub_self,zero_smul,one_smul,zero_add] using hz
    simp [hv0] at hv'
  let q : ℝ → V := fun t => unitRadial (p t)
  have hq : ContinuousOn q (Icc (0:ℝ) 1) :=
    (unitRadial_continuousOn (S := p '' Icc (0:ℝ) 1) (by rintro x ⟨t,ht,rfl⟩; exact hpz t ht)).comp hp.continuousOn (fun t ht => ⟨t,ht,rfl⟩)
  have hqn (t) (ht : t ∈ Icc (0:ℝ) 1) : ‖q t‖ = 1 := unitRadial_norm (hpz t ht)
  have hqW (t) : q t ∈ W := W.smul_mem _ (hpW t)
  have hq0 : q 0 = u := by simp only [q,p,sub_zero,one_smul,zero_smul,add_zero,unitRadial,hu,inv_one,one_smul]
  have hq1 : q 1 = v' := by simp only [q,p,sub_self,zero_smul,one_smul,zero_add,unitRadial,hv',inv_one,one_smul]
  have hcont : ContinuousOn (fun t => f (q t) i) (Icc (0:ℝ) 1) := (hf.smooth i).continuous.comp_continuousOn hq
  have hhalf : (1/2 : ℝ) ∈ Icc (f (q 1) i) (f (q 0) i) := by rw [hq0,hq1,hui',hv'i]; constructor <;> norm_num
  obtain ⟨t,ht,hth⟩ := intermediate_value_Icc' (zero_le_one : (0:ℝ) ≤ 1) hcont hhalf
  have hsum := hf.sum_two_labels (hqn t ht) hij (hzero (q t) (hqW t) (hqn t ht))
  exact hnot (q t) (hqn t ht) ⟨by linarith,by linarith⟩
end TwoLabels

end BorsukNine

end OAI
