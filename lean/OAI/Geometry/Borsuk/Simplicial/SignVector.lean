import Mathlib
import OAI.Geometry.Borsuk.Simplicial.LabelRegion

namespace OAI

namespace BorsukNine.SimplicialChains
open Finset

noncomputable def signVector (m : ℕ) (b : Fin m → Bool) : EuclideanSpace ℝ (Fin m) :=
  WithLp.toLp 2 (fun i => if b i then (-1:ℝ) else 1)

@[simp] lemma signVector_apply (m : ℕ) (b : Fin m → Bool) (i : Fin m) :
    signVector m b i = if b i then (-1:ℝ) else 1 := rfl

lemma signVector_norm (m : ℕ) (b : Fin m → Bool) : ‖signVector m b‖ = Real.sqrt m := by
  rw [EuclideanSpace.norm_eq]
  congr 1
  have h (i : Fin m) : ‖signVector m b i‖ ^ 2 = (1:ℝ) := by
    simp only [signVector_apply]
    cases b i <;> norm_num
  simp only [h, Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin, mul_one]

noncomputable def facetCenter (m : ℕ) (b : Fin m → Bool) : EuclideanSpace ℝ (Fin m) :=
  (Real.sqrt m)⁻¹ • signVector m b

lemma facetCenter_norm (m : ℕ) [NeZero m] (b : Fin m → Bool) : ‖facetCenter m b‖ = 1 := by
  rw [facetCenter, norm_smul, signVector_norm, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
  exact inv_mul_cancel₀ (ne_of_gt (Real.sqrt_pos_of_pos (by exact_mod_cast NeZero.pos m)))

lemma facetCenter_region (m : ℕ) (b : Fin m → Bool) (i : Fin m) :
    facetCenter m b ∈ labelRegion i (b i) := by
  have ha (j : Fin m) : |facetCenter m b j| = (Real.sqrt m)⁻¹ := by
    simp only [facetCenter, PiLp.smul_apply, smul_eq_mul, signVector_apply, abs_mul,
      abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
    cases b j <;> norm_num
  refine ⟨fun j => by rw [ha j,ha i],?_⟩
  change (if b i then (Real.sqrt m)⁻¹ * (if b i then (-1:ℝ) else 1) ≤ 0
    else 0 ≤ (Real.sqrt m)⁻¹ * (if b i then (-1:ℝ) else 1))
  have h := inv_nonneg.mpr (Real.sqrt_nonneg (m:ℝ))
  cases b i <;> simp_all

lemma all_labelRegions_iff_center (m : ℕ) [NeZero m] (b : Fin m → Bool)
    (y : EuclideanSpace ℝ (Fin m)) (hy : ‖y‖ = 1) :
    (∀ i, y ∈ labelRegion i (b i)) ↔ y = facetCenter m b := by
  refine ⟨?_,fun he i => he ▸ facetCenter_region m b i⟩
  intro hyc
  let i₀ : Fin m := ⟨0,NeZero.pos m⟩
  let d : ℝ := |y i₀|
  have hd : 0 ≤ d := abs_nonneg _
  have hcoord (i : Fin m) : |y i| = d :=
    le_antisymm ((hyc i₀).1 i) ((hyc i).1 i₀)
  have hv : y = d • signVector m b := by
    ext i
    simp only [PiLp.smul_apply, smul_eq_mul, signVector_apply]
    have hsign := (hyc i).2
    change (if b i then y i ≤ 0 else 0 ≤ y i) at hsign
    cases hb : b i
    · simp only [hb, Bool.false_eq_true, ↓reduceIte] at hsign ⊢
      simpa only [abs_of_nonneg hsign, mul_one] using hcoord i
    · simp only [hb, ↓reduceIte] at hsign ⊢
      have he := hcoord i
      rw [abs_of_nonpos hsign] at he
      linarith
  have hdval : d = (Real.sqrt m)⁻¹ := by
    have he := hy
    rw [hv,norm_smul,Real.norm_eq_abs,abs_of_nonneg hd,signVector_norm] at he
    exact eq_inv_of_mul_eq_one_left he
  rw [hv,hdval]
  rfl

lemma constant_approximation_facet_zero (n m r : ℕ) (hm : 1 < m) [NeZero m]
    (b : Fin m → Bool) (y : EuclideanSpace ℝ (Fin m)) :
    approximation n m r (fun _ => sphereLabel y) (crossFundamental n)
      ⟨crossFacet m b,crossFacet_mem m (NeZero.pos m) b⟩ = 0 := by
  classical
  let K := hemisphereComplex (n:ℝ) (E := EuclideanSpace ℝ (Fin n))
  let t : {s : Finset SignedVertex // s ∈ cross m} := ⟨crossFacet m b,crossFacet_mem m (NeZero.pos m) b⟩
  let T : Chain K →ₗ[F₂] F₂ := (Finsupp.lapply t).comp (mapChains K (cross m) (fun _ => sphereLabel y))
  change T (fineCrossMap n r (crossFundamental n)) = 0
  have ht : T = 0 := by
    apply Finsupp.lhom_ext
    intro s a
    have hh : T (simplex K s.val) = 0 := by
      change mapChains K (cross m) (fun _ => sphereLabel y) (simplex K s.val) t = 0
      rw [mapChains_simplex K (cross m) _ s.property]
      apply mapSimplex_coeff_zero_of_ne
      intro he
      have hc : (s.val.image (fun _ => sphereLabel y)).card ≤ 1 := by
        apply Finset.card_le_one.mpr
        intro a ha c hc
        obtain ⟨_,_,rfl⟩ := Finset.mem_image.mp ha
        obtain ⟨_,_,rfl⟩ := Finset.mem_image.mp hc
        rfl
      rw [he,crossFacet_card] at hc
      omega
    rw [simplex_of_mem K s.property] at hh
    have ha : Finsupp.single s a = a • Finsupp.single s (1:F₂) := by simp
    simp only [ha,map_smul,hh,smul_zero,LinearMap.zero_apply]
  rw [ht,LinearMap.zero_apply]

lemma continuous_missed_facet_zero (n m : ℕ) (hn : 0 < n) (hm : 1 < m) [NeZero m]
    (b : Fin m → Bool) (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (hf : ContinuousOn f (annulus n)) (hfn : ∀ x ∈ annulus n, ‖f x‖ = 1)
    (hmiss : ∀ x ∈ annulus n, f x ≠ facetCenter m b) :
    ∃ δ > 0, ∀ r : ℕ, (((n:ℝ)-1)/n)^r * 2 < δ →
      approximation n m r (fun x => sphereLabel (f x)) (crossFundamental n)
        ⟨crossFacet m b,crossFacet_mem m (NeZero.pos m) b⟩ = 0 := by
  have hfneg : -(facetCenter m b) ≠ facetCenter m b := by
    intro he
    have hz : facetCenter m b = 0 := by
      ext i
      have hi := congrArg (fun z : EuclideanSpace ℝ (Fin m) => z i) he
      simp only [PiLp.neg_apply] at hi
      change facetCenter m b i = 0
      linarith
    have hn := facetCenter_norm m b
    rw [hz,norm_zero] at hn
    exact zero_ne_one hn
  obtain ⟨δ,hδ,hh⟩ := localized_approximation_coeff n m hn b f (fun _ => -(facetCenter m b))
    hf continuousOn_const ∅ isOpen_empty (by simp) (by
      intro x hx
      rcases hx with h | h
      · exact False.elim (hmiss x.val x.property ((all_labelRegions_iff_center m b _ (hfn _ x.property)).mp h))
      · exact False.elim (hfneg ((all_labelRegions_iff_center m b _ (by simp [facetCenter_norm])).mp h)))
  refine ⟨δ,hδ,fun r hr => ?_⟩
  rw [hh r hr,constant_approximation_facet_zero n m r hm b]

end BorsukNine.SimplicialChains

end OAI
