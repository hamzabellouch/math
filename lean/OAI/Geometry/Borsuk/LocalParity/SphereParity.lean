import Mathlib
import OAI.Geometry.Borsuk.LocalParity.RegularModel
import OAI.Geometry.Borsuk.LocalParity.SphereNullPatch
import OAI.Geometry.Borsuk.LocalParity.SphereBlock

namespace OAI

open Set MeasureTheory
namespace BorsukNine
open Set SimplicialChains
open scoped RealInnerProductSpace
section SphereParity
variable {k : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
local notation "E" => EuclideanSpace ℝ (Fin (k+1))
local notation "W" => EuclideanSpace ℝ (Fin k)
omit [Fintype ι] in
lemma facetTail_point {I : Finset ι} (a : Fin (k+1) ≃ ↥I) (z : W) :
    facetTail a (facetPoint a z) = z := by
  ext j
  exact (facetPoint_apply a z j.succ).trans (simplexPoint_succ z j)
lemma Admissible.eq_facetPoint_of_tail {f : E → ι → ℝ} (hf : Admissible f)
    {I : Finset ι} (a : Fin (k+1) ≃ ↥I) {u : E} (hu : ‖u‖ = 1)
    (hs : positiveSupport f u ⊆ I) {z : W} (hz : facetTail a (f u) = z) :
    f u = facetPoint a z := by
  have he (i : ι) (hi : i ≠ (a 0).val) : f u i = facetPoint a z i := by
    by_cases hI : i ∈ I
    · obtain ⟨j,hj⟩ := a.surjective ⟨i,hI⟩
      have hji : (a j).val = i := congrArg Subtype.val hj
      have hj0 : j ≠ 0 := fun h => hi (by simpa only [h] using hji.symm)
      obtain ⟨l,rfl⟩ := Fin.eq_succ_of_ne_zero hj0
      rw [← hji,facetPoint_apply,simplexPoint_succ]
      exact congrArg (fun v : W => v l) hz
    · rw [facetPoint_zero a z hI]
      apply le_antisymm _ (hf.nonneg u hu i)
      exact le_of_not_gt (fun h => hI (hs ((mem_positiveSupport f u i).mpr h)))
  have hall : ∑ i, (f u i-facetPoint a z i) = f u (a 0).val-facetPoint a z (a 0).val := by
    apply Finset.sum_eq_single (a 0).val
    · intro i _ hi
      exact sub_eq_zero.mpr (he i hi)
    · simp
  rw [Finset.sum_sub_distrib,hf.sum_one u hu,facetPoint_sum,sub_self] at hall
  funext i
  by_cases hi : i = (a 0).val
  · subst i
    exact sub_eq_zero.mp hall.symm
  · exact he i hi

noncomputable def sphereRegularPatch (w c : E) (d : W →ₗᵢ[ℝ] E) (δ : ℝ) : Set (normSphere (k+1)) :=
  {u | 0 < ⟪w,u.val⟫ ∧ 0 < ⟪c,u.val⟫ ∧ ‖hemisphereInverse c d u.val‖ < δ}
lemma sphereRegularPatch_isOpen (w c : E) (d : W →ₗᵢ[ℝ] E) (δ : ℝ) :
    IsOpen (sphereRegularPatch w c d δ) := by
  have hc : IsOpen {u : E | 0 < ⟪c,u⟫} := isOpen_lt continuous_const (continuous_const.inner continuous_id)
  have hp := (hemisphereInverse_continuousOn c d).norm.isOpen_inter_preimage hc (isOpen_Iio : IsOpen (Iio δ))
  exact ((isOpen_lt (f := fun u : E => (0 : ℝ)) (g := fun u : E => ⟪w,u⟫) continuous_const (continuous_const.inner continuous_id)).inter hp).preimage continuous_subtype_val

lemma Admissible.regular_facet_level_even {f : E → ι → ℝ} (hf : Admissible f)
    (hk : 0 < k) {I : Finset ι} (a : Fin (k+1) ≃ ↥I)
    (hfree : ∀ u : E, ‖u‖ = 1 → (∀ j : Fin k, 0 < f u (a j.succ).val) → positiveSupport f u ⊆ I)
    {w : E} (hw : ‖w‖ = 1) (hwi : ∀ i ∈ I, 0 < f w i)
    (e : W →ₗᵢ[ℝ] E) (he : ∀ v, ⟪w,e v⟫ = 0)
    (hes : ∀ u, ⟪w,u⟫ = 0 → ∃ v, e v = u) {z : W} (hz : z ∈ simplexInterior k)
    (hr : ∀ v, baseCoordinates f w e a v = z → (fderiv ℝ (baseCoordinates f w e a) v).det ≠ 0)
    (hfin : (orientedLevel f w (facetPoint a z)).Finite) :
    (Nat.card (orientedLevel f w (facetPoint a z)) : F₂) = 0 := by
  classical
  let L := orientedLevel f w (facetPoint a z)
  let : Fintype L := hfin.fintype
  have hI : I.Nonempty := ⟨(a 0).val,(a 0).property⟩
  have hc (c : L) : ‖c.val‖ = 1 := c.property.1
  have hcv (c : L) : f c.val = facetPoint a z := c.property.2.1
  have hcw (c : L) : 0 < ⟪w,c.val⟫ := hf.orientedLevel_inner_pos hI hw hwi (facetPoint_pos a hz) c.property
  have hdata (c : L) := hf.regular_model_data a hw (hc c) e he hes (hcw c) (hcv c) hr
  choose d D δ hd hds hδ hreg using hdata
  let g : E → W := fun u => facetTail a (f u)
  have hg : Continuous g := (facetTail a).continuous_of_finiteDimensional.comp (continuous_pi (fun i => (hf.smooth i).continuous))
  let C : ℝ × normSphere (k+1) → E := fun p => sphereBlock ⟪w,p.2.val⟫ (p.1 • g p.2.val-z)
  have hC : Continuous C := sphereBlock_continuous (continuous_const.inner continuous_snd.subtype_val)
    ((continuous_fst.smul (hg.comp continuous_snd.subtype_val)).sub continuous_const)
  have hCz (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) (u : normSphere (k+1)) : C (t,u) ≠ 0 := by
    intro hzero
    obtain ⟨hwu,hv⟩ := sphereBlock_eq_zero hzero
    have htail : g u.val = 0 := by
      ext j
      apply le_antisymm _ (hf.nonneg _ u.property _)
      exact le_of_not_gt (fun hp => hf.orthogonal w u.val hw u.property hwu (a j.succ).val ⟨hwi _ (a j.succ).property,hp⟩)
    change t • g u.val-z = 0 at hv
    rw [htail,smul_zero,zero_sub,neg_eq_zero] at hv
    have hpos := hz.1 (⟨0,hk⟩ : Fin k)
    rw [hv] at hpos
    exact lt_irrefl 0 hpos
  let F : normSphere (k+1) → E := fun u => sphereBlock ⟪w,u.val⟫ (g u.val-z)
  have hF : Continuous F := sphereBlock_continuous (continuous_const.inner continuous_subtype_val)
    ((hg.comp continuous_subtype_val).sub continuous_const)
  have hFz (u) : F u ≠ 0 := by simpa only [C,F,one_smul] using hCz 1 ⟨zero_le_one,le_rfl⟩ u
  let G : L → normSphere (k+1) → E := fun c u => sphereBlockModel c.val (d c) (D c) u.val
  let K : L → Set (normSphere (k+1)) := fun c => {u | u.val = c.val}
  let S : L → Set (normSphere (k+1)) := fun c => sphereRegularPatch w c.val (d c) (δ c)
  let y : E := sphereBlock 1 (0 : W)
  have hy : y ≠ 0 := fun h => one_ne_zero (sphereBlock_eq_zero h).1
  have hKS (c : L) : K c ⊆ S c := by
    intro u hu
    change u.val = c.val at hu
    change 0 < ⟪w,u.val⟫ ∧ 0 < ⟪c.val,u.val⟫ ∧ ‖hemisphereInverse c.val (d c) u.val‖ < δ c
    rw [hu,real_inner_self_eq_norm_sq,hc c,one_pow]
    refine ⟨hcw c,zero_lt_one,?_⟩
    rw [hemisphereInverse,adjoint_normal c.val (d c) (hd c),smul_zero,norm_zero]
    exact hδ c
  have hKd : Pairwise (fun c c' => Disjoint (K c) (K c')) := by
    intro c c' hcc
    apply Set.disjoint_left.mpr
    intro u hu hu'
    exact hcc (Subtype.ext (hu.symm.trans hu'))
  have hmiss (u : normSphere (k+1)) : ¬ ∃ b : ℝ, 0 < b ∧ C (0,u) = b • y := by
    rintro ⟨b,hb,hbEq⟩
    have hv := congrArg (fun v : E => v (Fin.succ ⟨0,hk⟩)) hbEq
    have hpos := hz.1 (⟨0,hk⟩ : Fin k)
    simp only [C,y,zero_smul,zero_sub,sphereBlock_succ,PiLp.neg_apply,PiLp.smul_apply,PiLp.zero_apply,smul_eq_mul,mul_zero] at hv
    linarith
  have hcover (u : normSphere (k+1)) (hu : ∃ b : ℝ, 0 < b ∧ F u = b • y) : ∃ c, u ∈ K c := by
    obtain ⟨b,hb,hbu⟩ := hu
    have hwu : 0 < ⟪w,u.val⟫ := by
      have hh := congrArg (fun v : E => v 0) hbu
      have hh' : ⟪w,u.val⟫ = b := by simpa only [F,y,sphereBlock_zero,PiLp.smul_apply,smul_eq_mul,mul_one] using hh
      exact hh' ▸ hb
    have hgz : g u.val = z := by
      ext j
      have hh := congrArg (fun v : E => v j.succ) hbu
      have hh' : g u.val j-z j = 0 := by simpa only [F,y,sphereBlock_succ,PiLp.sub_apply,PiLp.smul_apply,PiLp.zero_apply,smul_eq_mul,mul_zero] using hh
      exact sub_eq_zero.mp hh'
    have hup : ∀ j : Fin k, 0 < f u.val (a j.succ).val := by
      intro j
      have hh := congrArg (fun v : W => v j) hgz
      change f u.val (a j.succ).val = z j at hh
      rw [hh]
      exact hz.1 j
    have huf := hf.eq_facetPoint_of_tail a u.property (hfree u.val u.property hup) hgz
    exact ⟨⟨u.val,u.property,huf,hwu.le⟩,rfl⟩
  have hcount := sphere_null_patch_models (by omega : 1 < k+1) F hF hFz C hC.continuousOn hCz
    (fun u => by simp only [C,F,one_smul]) G
    (fun c => (sphereBlockModel_continuous c.val (d c) (D c)).comp continuous_subtype_val)
    (fun c u => sphereBlockModel_ne_zero (hc c) (d c) (hd c) (hds c) (D c) (norm_ne_zero_iff.mp (by rw [u.property]; exact one_ne_zero)))
    (by intro c u v hv; simp only [G,hv,sphereBlockModel_odd]) K S
    (fun c => isClosed_eq continuous_subtype_val continuous_const)
    (fun c => sphereRegularPatch_isOpen w c.val (d c) (δ c)) hKS hKd hy hmiss hcover
    (by
      intro c u hu
      obtain ⟨b,hb,hbu⟩ := hu
      exact sphereBlockModel_ray (hc c) u.property (d c) (hd c) (hds c) (D c) hb hbu)
    (by
      intro c u hu t ht
      exact sphereBlock_mix_nonzero (d c) (D c) (g u.val-z) hu.1 hu.2.1 ht)
    (by
      intro c u hu t ht htu
      obtain ⟨b,hb,hbu⟩ := htu
      apply sphereBlock_mix_ray (hc c) u.property (d c) (hd c) (hds c) (D c) (g u.val-z) hu.2.1 _ ht hbu
      have hge : g u.val-z = facetTail a (f u.val-f c.val) := by
        rw [map_sub,hcv c,facetTail_point]
      rw [hge]
      exact hreg c u.val u.property hu.2.1 hu.2.2)
  simpa only [Nat.card_eq_fintype_card] using hcount
end SphereParity
end BorsukNine

end OAI
