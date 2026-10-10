import OAI.Algebra.Determinantal.Transcendence

namespace OAI

namespace PermanentBorder.SliceParameters
open MvPolynomial

lemma singularSystem_map {K L β : Type*} [CommRing K] [CommRing L]
    (φ : K →+* L) (f : MvPolynomial β K) (j : Option β) :
    map φ (singularSystem f j) = singularSystem (map φ f) j := by
  cases j with
  | none => rfl
  | some i => exact pderiv_map.symm

noncomputable def universalSection {σ α β : Type*} [Fintype β]
    (F : MvPolynomial α (MvPolynomial σ ℤ)) :
    MvPolynomial β (MvPolynomial (σ ⊕ (α × β)) ℤ) :=
  linearSection (fun i => X (Sum.inr i)) (map (rename (R := ℤ) (fun i : σ => (Sum.inl i : σ ⊕ (α × β)))).toRingHom F)

lemma universalSection_specialize {K σ α β : Type*} [CommRing K] [Fintype β]
    (F : MvPolynomial α (MvPolynomial σ ℤ)) (θ : σ → K) (H : α × β → K) :
    map (eval₂Hom (Int.castRingHom K) (Sum.elim θ H)) (universalSection F) =
      linearSection H (map (eval₂Hom (Int.castRingHom K) θ) F) := by
  rw [universalSection, linearSection_map, map_map]
  have he : (eval₂Hom (Int.castRingHom K) (Sum.elim θ H)).comp (rename (R := ℤ) (fun i : σ => (Sum.inl i : σ ⊕ (α × β)))).toRingHom =
      eval₂Hom (Int.castRingHom K) θ := by
    ext i <;> simp
  rw [he]
  have hH : (fun i : α × β =>
      eval₂Hom (Int.castRingHom K) (Sum.elim θ H) (X (Sum.inr i))) = H := by
    funext i
    exact eval₂_X _ _ _
  rw [hH]

lemma universalSection_macaulay_map {M σ α β : Type*} [Field M] [Fintype β]
    (F : MvPolynomial α (MvPolynomial σ ℤ)) (r D : ℕ)
    (t : σ → M) (A : α × β → M) :
    (macaulayMatrix (singularDegrees r)
      (singularSystem (universalSection (β := β) F)) D).map
        (eval₂Hom (Int.castRingHom M) (Sum.elim t A)) =
      macaulayMatrix (singularDegrees r)
        (singularSystem (linearSection A (map (eval₂Hom (Int.castRingHom M) t) F))) D := by
  rw [← macaulayMatrix_map]
  apply congrArg (fun Q => macaulayMatrix (singularDegrees r) Q D)
  funext j
  rw [singularSystem_map, universalSection_specialize]

theorem transfer_section_certificate {K L σ α β : Type*}
    [Field K] [Field L] [CharZero L] [Infinite L] [Fintype β]
    (F : MvPolynomial α (MvPolynomial σ ℤ)) (r D : ℕ)
    (θ : σ → K) (H : α × β → K)
    (h : Function.Surjective
      (macaulayMatrix (singularDegrees r)
        (singularSystem (linearSection H
          (map (eval₂Hom (Int.castRingHom K) θ) F))) D).mulVec) :
    ∃ θ' : σ → L, ∃ H' : α × β → L,
      Function.Surjective
        (macaulayMatrix (singularDegrees r)
          (singularSystem (linearSection H'
            (map (eval₂Hom (Int.castRingHom L) θ') F))) D).mulVec := by
  classical
  let P := macaulayMatrix (singularDegrees r) (singularSystem (universalSection (β := β) F)) D
  have hp : Function.Surjective
      (P.map (eval₂Hom (Int.castRingHom K) (Sum.elim θ H))).mulVec := by
    dsimp only [P]
    rwa [universalSection_macaulay_map]
  obtain ⟨w,hw⟩ := integer_polynomial_rank_transfer (L := L) P (Sum.elim θ H) hp
  refine ⟨fun i => w (Sum.inl i), fun i => w (Sum.inr i), ?_⟩
  have hw' : Sum.elim (fun i => w (Sum.inl i)) (fun i => w (Sum.inr i)) = w := by
    funext i
    cases i <;> rfl
  dsimp only [P] at hw
  rw [← universalSection_macaulay_map, hw']
  exact hw

end PermanentBorder.SliceParameters

namespace PermanentBorder.SliceParameters
open MvPolynomial

lemma macaulay_no_nonzero_zero {K σ ι : Type*} [Field K] [Fintype σ] [Fintype ι]
    (e : ι → ℤ) (F : ι → MvPolynomial σ K)
    (hF : ∀ i, (F i).IsWeightedHomogeneous (fun _ : σ => (1 : ℤ)) (e i)) (D : ℕ)
    (h : Function.Surjective (macaulayMatrix e F D).mulVec)
    (y : σ → K) (hy : ∀ i, eval y (F i) = 0) : y = 0 := by
  classical
  have hz : y ∈ zeroLocus K (Ideal.span (Set.range F)) := by
    rw [zeroLocus_span]
    rintro _ ⟨i,rfl⟩
    exact hy i
  have hD := (macaulay_surjective_iff e F hF D).mp h
  ext j
  have hx : (X j : MvPolynomial σ K)^D ∈ Ideal.span (Set.range F) :=
    hD _ (homogeneous_intWeight (by simpa only [one_mul] using (isHomogeneous_X K j).pow D))
  have hv : y j ^ D = 0 := by simpa using hz _ hx
  by_contra hj
  exact pow_ne_zero D hj hv

theorem certificate_smooth_equations {K β : Type*} [Field K] [Fintype β]
    (g : MvPolynomial β K) (r D : ℕ) (hg : g.IsHomogeneous r)
    (h : Function.Surjective
      (macaulayMatrix (singularDegrees r) (singularSystem g) D).mulVec) :
    ∀ y : β → K, eval y g = 0 → (∀ j, eval y (pderiv j g) = 0) → y = 0 := by
  intro y hy hd
  apply macaulay_no_nonzero_zero _ _ (singularSystem_homogeneous hg) D h y
  intro j
  cases j with
  | none => exact hy
  | some j => exact hd j

end PermanentBorder.SliceParameters

namespace PermanentBorder.SliceParameters
open MvPolynomial
universe u v
variable (K : Type u) [Field K] (ι : Type v)

abbrev GenericClosed := AlgebraicClosure (FractionRing (MvPolynomial ι K))

noncomputable def independentParameters : ι → GenericClosed K ι := fun i =>
  algebraMap (FractionRing (MvPolynomial ι K)) (GenericClosed K ι)
    (algebraMap (MvPolynomial ι K) (FractionRing (MvPolynomial ι K)) (X i))

lemma independentParameters_independent : AlgebraicIndependent K (independentParameters K ι) := by
  let R := MvPolynomial ι K
  let Q := FractionRing R
  have hQ : AlgebraicIndependent K (fun i : ι => algebraMap R Q (X i)) :=
    (MvPolynomial.algebraicIndependent_X ι K).map'
      (f := IsScalarTower.toAlgHom K R Q) (IsFractionRing.injective R Q)
  exact hQ.map' (f := IsScalarTower.toAlgHom K Q (GenericClosed K ι))
    (RingHom.injective (algebraMap Q (GenericClosed K ι)))

end PermanentBorder.SliceParameters

namespace PermanentBorder.SliceParameters
open MvPolynomial
universe u v

lemma specialize_tower {K L σ α : Type*} [CommRing K] [CommRing L]
    (φ : K →+* L) (F : MvPolynomial α (MvPolynomial σ ℤ)) (θ : σ → K) :
    map φ (map (eval₂Hom (Int.castRingHom K) θ) F) =
      map (eval₂Hom (Int.castRingHom L) (fun i => φ (θ i))) F := by
  rw [map_map]
  apply congrArg (fun ψ : MvPolynomial σ ℤ →+* L => map ψ F)
  ext i <;> simp

theorem exists_complex_smooth_section {K : Type u} [Field K] {σ : Type v}
    {v d n r : ℕ} (F : MvPolynomial (Fin (v+1)) (MvPolynomial σ ℤ))
    (hF : F.IsHomogeneous r) (θ : σ → K)
    (hf : map (eval₂Hom (Int.castRingHom K) θ) F ≠ 0)
    (hdim : ringKrullDim (MvPolynomial (Fin (v+1)) K ⧸
      Ideal.span (Set.range (fun i => pderiv i
        (map (eval₂Hom (Int.castRingHom K) θ) F)))) ≤ n)
    (hn : n+d < v+1) :
    ∃ θ' : σ → ℂ, ∃ H' : Fin (v+1) × Fin (d+1) → ℂ,
      let g := linearSection H' (map (eval₂Hom (Int.castRingHom ℂ) θ') F)
      g ≠ 0 ∧ g.IsHomogeneous r ∧
      (∀ y : Fin (d+1) → ℂ, eval y g = 0 →
        (∀ j, eval y (pderiv j g) = 0) → y = 0) := by
  classical
  let M := GenericClosed K (Fin (v+1) × Fin (d+1))
  let H := independentParameters K (Fin (v+1) × Fin (d+1))
  obtain ⟨D,hD⟩ := generic_slice_certificate
    (L := M) _ hf (hF.map _) hdim hn H (independentParameters_independent K _)
  rw [specialize_tower] at hD
  obtain ⟨t,A,hA⟩ := transfer_section_certificate (L := ℂ) F r D
    (fun i => algebraMap K M (θ i)) H hD
  refine ⟨t,A, ?_⟩
  let g := linearSection A (map (eval₂Hom (Int.castRingHom ℂ) t) F)
  have hg : g.IsHomogeneous r := linearSection_homogeneous A (hF.map _)
  have hs := certificate_smooth_equations g r D hg hA
  refine ⟨?_,hg,hs⟩
  intro h
  change g = 0 at h
  have hzero := hs (fun _ => 1) (by rw [h, map_zero]) (by
    intro j
    rw [h, map_zero, map_zero])
  exact one_ne_zero (congrFun hzero (0 : Fin (d+1)))

end PermanentBorder.SliceParameters
namespace PermanentBorder.SliceParameters
open MvPolynomial

lemma gradientIdeal_rename {K α β : Type*} [CommRing K]
    (e : α ≃ β) (f : MvPolynomial α K) :
    Ideal.span (Set.range (fun j => pderiv j (rename e f))) =
      (Ideal.span (Set.range (fun i => pderiv i f))).map
        (renameEquiv K e).toRingEquiv.toRingHom := by
  rw [Ideal.map_span]
  congr 1
  ext p
  constructor
  · rintro ⟨j,rfl⟩
    refine ⟨pderiv (e.symm j) f,⟨e.symm j,rfl⟩,?_⟩
    change rename e (pderiv (e.symm j) f) = pderiv j (rename e f)
    rw [← pderiv_rename e.injective,e.apply_symm_apply]
  · rintro ⟨_,⟨i,rfl⟩,rfl⟩
    exact ⟨e i,pderiv_rename e.injective i f⟩

lemma gradientDimension_rename {K α β : Type*} [CommRing K]
    (e : α ≃ β) (f : MvPolynomial α K) :
    ringKrullDim (MvPolynomial β K ⧸ Ideal.span (Set.range (fun j => pderiv j (rename e f)))) =
      ringKrullDim (MvPolynomial α K ⧸ Ideal.span (Set.range (fun i => pderiv i f))) := by
  exact ringKrullDim_eq_of_ringEquiv
    (Ideal.quotientEquiv _ _ (renameEquiv K e).toRingEquiv (gradientIdeal_rename e f)).symm

lemma nonzero_of_gradientDimension {K α : Type*} [Field K] [Fintype α]
    (f : MvPolynomial α K) (n : ℕ)
    (hdim : ringKrullDim (MvPolynomial α K ⧸
      Ideal.span (Set.range (fun i => pderiv i f))) ≤ n)
    (hn : n < Fintype.card α) : f ≠ 0 := by
  intro h
  rw [h] at hdim
  have hz : Ideal.span (Set.range (fun i : α => pderiv i (0 : MvPolynomial α K))) = ⊥ := by
    apply le_antisymm _ bot_le
    apply Ideal.span_le.mpr
    rintro _ ⟨i,rfl⟩
    simp
  rw [hz,ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot _),
    MvPolynomial.ringKrullDim_of_isNoetherianRing] at hdim
  have hdim' : ((Fintype.card α : ℕ) : WithBot ℕ∞) ≤ n := by simpa using hdim
  have hi : Fintype.card α ≤ n := by exact_mod_cast hdim'
  omega

theorem exists_complex_smooth_section_finite {K α σ : Type} [Field K] [Fintype α]
    {v d n r : ℕ} (hv : Fintype.card α = v+1)
    (F : MvPolynomial α (MvPolynomial σ ℤ)) (hF : F.IsHomogeneous r) (θ : σ → K)
    (hf : map (eval₂Hom (Int.castRingHom K) θ) F ≠ 0)
    (hdim : ringKrullDim (MvPolynomial α K ⧸
      Ideal.span (Set.range (fun i => pderiv i
        (map (eval₂Hom (Int.castRingHom K) θ) F)))) ≤ n)
    (hn : n+d < v+1) :
    ∃ θ' : σ → ℂ, ∃ H' : α × Fin (d+1) → ℂ,
      let g := linearSection H' (map (eval₂Hom (Int.castRingHom ℂ) θ') F)
      g ≠ 0 ∧ g.IsHomogeneous r ∧
      (∀ y : Fin (d+1) → ℂ, eval y g = 0 →
        (∀ j, eval y (pderiv j g) = 0) → y = 0) := by
  classical
  let e : α ≃ Fin (v+1) := Fintype.equivFinOfCardEq hv
  let F' := rename e F
  have he (L : Type) [CommRing L] (t : σ → L) :
      map (eval₂Hom (Int.castRingHom L) t) F' =
        rename e (map (eval₂Hom (Int.castRingHom L) t) F) := by
    exact map_rename _ _ _
  have hf' : map (eval₂Hom (Int.castRingHom K) θ) F' ≠ 0 := by
    rw [he]
    exact fun h => hf ((rename_injective _ e.injective).eq_iff.mp (h.trans (map_zero _).symm))
  have hd' : ringKrullDim (MvPolynomial (Fin (v+1)) K ⧸
      Ideal.span (Set.range (fun i => pderiv i
        (map (eval₂Hom (Int.castRingHom K) θ) F')))) ≤ n := by
    rw [he,gradientDimension_rename]
    exact hdim
  obtain ⟨t,H,hh⟩ := exists_complex_smooth_section F' hF.rename_isHomogeneous θ hf' hd' hn
  refine ⟨t,(fun ij => H (e ij.1,ij.2)),?_⟩
  have hl (f : MvPolynomial α ℂ) :
      linearSection H (rename e f) = linearSection (fun ij => H (e ij.1,ij.2)) f := by
    have hhom : (linearSection H).comp (rename e) =
        linearSection (fun ij => H (e ij.1,ij.2)) := by
      apply MvPolynomial.algHom_ext
      intro i
      simp only [AlgHom.comp_apply,rename_X,linearSection_X]
      rfl
    exact DFunLike.congr_fun hhom f
  rw [he,hl] at hh
  exact hh
end PermanentBorder.SliceParameters

namespace PermanentBorder.Parameters

abbrev auxiliarySize (m : ℕ) := m / 11
abbrev selectorIndex (k : ℕ) := (k-1) / 3
abbrev selectorDegree (k : ℕ) := k - 2 * selectorIndex k
abbrev defectThreshold (k : ℕ) := (selectorIndex k + 2).choose 2
abbrev codimension (k : ℕ) := defectThreshold k - 2*k
abbrev sectionDimension (k : ℕ) := k^2 / 100

theorem size_bound {m : ℕ} (hm : 1408 ≤ m) :
    128 ≤ auxiliarySize m ∧ (m : ℝ) / 12 ≤ auxiliarySize m ∧
    11 * auxiliarySize m ≤ m := by
  dsimp [auxiliarySize]
  have h : m ≤ 12 * (m / 11) := by omega
  refine ⟨by omega, ?_, by omega⟩
  have hr : (m : ℝ) ≤ 12 * (m / 11 : ℕ) := by exact_mod_cast h
  linarith

theorem index_bounds {k : ℕ} (hk : 128 ≤ k) :
    (k : ℝ) / 4 ≤ selectorIndex k ∧ selectorIndex k ≤ k / 2 ∧
    (k : ℝ) / 4 ≤ (selectorDegree k - 1 : ℕ) ∧
    2 ≤ selectorDegree k := by
  have hq : k ≤ 4 * selectorIndex k := by dsimp [selectorIndex]; omega
  have hr : k ≤ 4 * (selectorDegree k - 1) := by
    dsimp [selectorDegree, selectorIndex]; omega
  refine ⟨?_, by dsimp [selectorIndex]; omega, ?_, ?_⟩
  · have hc : (k : ℝ) ≤ 4 * selectorIndex k := by exact_mod_cast hq
    linarith
  · have hc : (k : ℝ) ≤ 4 * (selectorDegree k - 1 : ℕ) := by exact_mod_cast hr
    linarith
  · dsimp [selectorDegree, selectorIndex]; omega

theorem defect_formula (k : ℕ) :
    (defectThreshold k : ℝ) =
      ((selectorIndex k : ℝ)+2) * ((selectorIndex k : ℝ)+1) / 2 := by
  simp only [defectThreshold, Nat.cast_choose_two, Nat.cast_add, Nat.cast_ofNat]
  ring

theorem codimension_bounds {k : ℕ} (hk : 128 ≤ k) :
    (k : ℝ)^2 / 64 ≤ codimension k ∧ 1 ≤ codimension k ∧
    codimension k ≤ k^2 := by
  have hkR : (128 : ℝ) ≤ k := by exact_mod_cast hk
  have hq := (index_bounds hk).1
  have hq0 : (0 : ℝ) ≤ selectorIndex k := Nat.cast_nonneg _
  have hqU : (selectorIndex k : ℝ) ≤ (k : ℝ)/3 := by
    have : 3 * selectorIndex k ≤ k := by dsimp [selectorIndex]; omega
    have hc : (3:ℝ)*selectorIndex k ≤ k := by exact_mod_cast this
    linarith
  have hT := defect_formula k
  have hlow : (k : ℝ)^2 / 32 ≤ defectThreshold k := by
    nlinarith [sq_nonneg ((selectorIndex k : ℝ) - (k : ℝ)/4)]
  have hdelta : (k : ℝ)^2/64 ≤ (defectThreshold k : ℝ) - 2*k := by
    nlinarith [mul_nonneg (show 0 ≤ (k : ℝ) from by positivity) (sub_nonneg.mpr hkR)]
  have hsub : 2*k ≤ defectThreshold k := by
    have : (2*k : ℝ) ≤ defectThreshold k := by nlinarith [sq_nonneg (k : ℝ)]
    exact_mod_cast this
  have hd : (codimension k : ℝ) = (defectThreshold k : ℝ) - 2*k := by
    rw [codimension, Nat.cast_sub hsub, Nat.cast_mul, Nat.cast_ofNat]
  have hupper : (defectThreshold k : ℝ) < (k : ℝ)^2 := by
    nlinarith [mul_nonpos_of_nonpos_of_nonneg (show (selectorIndex k : ℝ) - k/3 ≤ 0 by linarith)
      (show (0:ℝ) ≤ (selectorIndex k : ℝ) + k/3 + 3 by positivity)]
  refine ⟨by simpa only [hd] using hdelta, ?_, ?_⟩
  · have : (1 : ℝ) ≤ codimension k := by rw [hd]; nlinarith [sq_nonneg ((k : ℝ)-128)]
    exact_mod_cast this
  · have : (codimension k : ℝ) ≤ (k : ℝ)^2 := by rw [hd]; nlinarith
    exact_mod_cast this

theorem section_bounds {k : ℕ} (hk : 128 ≤ k) :
    2 ≤ sectionDimension k ∧ sectionDimension k < k^2 ∧
    sectionDimension k - 1 < codimension k ∧
    (k : ℝ)^2 / 200 ≤ (sectionDimension k - 1 : ℕ) := by
  have hk2 : 16384 ≤ k^2 := by nlinarith
  have hd2 : 2 ≤ sectionDimension k := by dsimp [sectionDimension]; omega
  have hcast : (k : ℝ)^2 < 100*((sectionDimension k : ℝ)+1) := by
    have : k^2 < 100*(sectionDimension k+1) := by dsimp [sectionDimension]; omega
    exact_mod_cast this
  have hcast2 : 100*(sectionDimension k : ℝ) ≤ (k : ℝ)^2 := by
    have : 100*sectionDimension k ≤ k^2 := by dsimp [sectionDimension]; omega
    exact_mod_cast this
  have hkR : (128 : ℝ) ≤ k := by exact_mod_cast hk
  have hm : ((sectionDimension k - 1 : ℕ) : ℝ) = sectionDimension k - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  refine ⟨hd2, by dsimp [sectionDimension]; omega, ?_, ?_⟩
  · have hδ := (codimension_bounds hk).1
    have : ((sectionDimension k - 1 : ℕ) : ℝ) < codimension k := by
      rw [hm]
      nlinarith [sq_nonneg (k : ℝ)]
    exact_mod_cast this
  · rw [hm]
    nlinarith [sq_nonneg ((k : ℝ)-128)]

theorem explicit_constant {m : ℕ} (hm : 1408 ≤ m) :
    (m : ℝ)^3 / (5529600 * Real.exp 1) ≤
      (((selectorDegree (auxiliarySize m) - 1 : ℕ) : ℝ) *
       ((sectionDimension (auxiliarySize m) - 1 : ℕ) : ℝ)) / (4 * Real.exp 1) := by
  let k := auxiliarySize m
  have hk : 128 ≤ k := (size_bound hm).1
  have hmk : (m : ℝ)/12 ≤ k := (size_bound hm).2.1
  have hr := (index_bounds hk).2.2.1
  have hd := (section_bounds hk).2.2.2
  have hprod : (k : ℝ)^3 / 800 ≤
      ((selectorDegree k - 1 : ℕ) : ℝ) * ((sectionDimension k - 1 : ℕ) : ℝ) := by
    have hmul := mul_le_mul hr hd (by positivity : (0:ℝ) ≤ (k : ℝ)^2 / 200)
      (by positivity : (0:ℝ) ≤ ((selectorDegree k - 1 : ℕ) : ℝ))
    nlinarith
  have hcubes : (m : ℝ)^3 ≤ 1728 * (k : ℝ)^3 := by
    have := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ (m:ℝ))
      (show (m : ℝ) ≤ 12 * k by linarith) 3
    nlinarith
  have he := Real.exp_pos (1 : ℝ)
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  dsimp [k] at hprod hcubes ⊢
  nlinarith

end PermanentBorder.Parameters

namespace PermanentBorder
open MvPolynomial
lemma SliceParameters.linearSection_eq_affineSubstitution {α β : Type*}
    [Fintype β] (H : α × β → ℂ) :
    SliceParameters.linearSection H = affineSubstitution (fun _ => 0) (fun i j => H (i,j)) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp [SliceParameters.linearSection,SliceParameters.sectionForm,affineSubstitution]

theorem HasBorderDeterminant.selector_lower_of_critical_dimension
    {K : Type} [Field K] {m n k q d B : ℕ}
    (h : HasBorderDeterminant n (permanentPolynomial m))
    (hk : 0 < k) (hq : q ≤ k) (hr : 2 ≤ k-2*q) (hd : 2 ≤ d)
    (hm : 11*k-2*q ≤ m) (θ : Fin k → K)
    (hdim : ringKrullDim (MvPolynomial (Variables k) K ⧸
      Ideal.span (Set.range (fun i => pderiv i
        (Selector.diagonalCoefficient
          (Matrix.of fun a b => (X (a,b) : MvPolynomial (Variables k) K))
          (fun i => C (θ i)) q)))) ≤ B)
    (hB : B+(d-1) < k^2) :
    (((k-2*q-1 : ℕ) : ℝ) * ((d-1 : ℕ) : ℝ)) / (4*Real.exp 1) ≤ n := by
  classical
  have hk2 : 0 < k^2 := pow_pos hk _
  have hc : Fintype.card (Variables k) = k^2 := by simp [Variables,pow_two]
  have hv : Fintype.card (Variables k) = (k^2-1)+1 := by omega
  let F : MvPolynomial (Variables k) (MvPolynomial (Fin k) ℤ) :=
    Selector.integralCoefficientFamily k q
  have hd' : ringKrullDim (MvPolynomial (Variables k) K ⧸
      Ideal.span (Set.range (fun i => pderiv i
        (map (eval₂Hom (Int.castRingHom K) θ) F)))) ≤ B := by
    rw [show map (eval₂Hom (Int.castRingHom K) θ) F =
      Selector.diagonalCoefficient
        (Matrix.of fun a b => (X (a,b) : MvPolynomial (Variables k) K))
        (fun i => C (θ i)) q from Selector.integralCoefficientFamily_specialize k q θ]
    exact hdim
  have hFne := SliceParameters.nonzero_of_gradientDimension
    (map (eval₂Hom (Int.castRingHom K) θ) F) B hd' (by omega : B < Fintype.card (Variables k))
  obtain ⟨t,H,hs⟩ := SliceParameters.exists_complex_smooth_section_finite hv F
    (Selector.integralCoefficientFamily_homogeneous k q) θ hFne hd'
    (by omega : B+(d-1) < (k^2-1)+1)
  have hb := (h.coefficientPolynomial hq hm t).affineSubstitution
    (fun _ => 0) (fun i j => H (i,j))
  rw [← SliceParameters.linearSection_eq_affineSubstitution,
    ← Selector.integralCoefficientFamily_complex] at hb
  have he := Polar.HasBorderDeterminant.smooth_lower_bound hb
    (by simpa only [Fintype.card_fin] using (show 2 ≤ d-1+1 by omega)) hr hs.2.1 hs.2.2
  simpa only [Fintype.card_fin,Nat.add_sub_cancel] using he
end PermanentBorder

namespace PermanentBorder
open MvPolynomial Parameters

end PermanentBorder

end OAI
