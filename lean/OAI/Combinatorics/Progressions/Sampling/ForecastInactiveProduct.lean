import OAI.Combinatorics.Progressions.Geometry.AllocatedMixedFixedSupport

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)

theorem exists_forecast_inactive_zero_axis_site
    (j : Fin m) (i : Fin (n j)) (q : ℕ) (hq : 0 < q)
    [Nonempty (B ⟨j, Sum.inr i⟩)]
    (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option Empty → ZMod q)
    {D P p v ε E : ℝ}
    (hD : AllocatedComparisonDimensions (G := G) B Empty
      (fun _ : Fin m => ((Finset.univ : Finset (Finset Empty)) : Type)) D)
    (hP : 1 ≤ P) (hp : 0 ≤ p) (hv : 0 ≤ v)
    (hPp : P ≤ Real.exp p) (hqv : (q : ℝ) ≤ Real.exp v)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hE : 0 ≤ E) (hεE : ε⁻¹ ≤ Real.exp E)
    (hsize : q ≤ S.value) (hR1 : R j ≤ 1)
    (hsmall : basisAxisScale (b j) i ≤ S.value ^ (j.val + 1))
    (hcell : 0 < (principalTupleWeights (α := Empty) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
        (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
    (hgrid : allocatedGridAxis (I := I) U b S.value ⟨j, Sum.inr i⟩)
    (hσ1 : σ j ≤ 1) (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition)
    (hprimitive : scalarCubePrimitiveEnvelope Empty A 1 0 q ≤ P)
    (hB : uniformSpectrumBlockCount j.val 1 (j.val + 1) ≤ Fintype.card (B ⟨j, Sum.inr i⟩)) :
    let scale := allocatedPrincipalGridScale (G := G) B U b (R := R) j i
    let O := allocatedInactiveSiteOutputLog m D p v E
    ∃ e : ScalarSiteExpansion.{0,0} (Finset Empty),
      e.Bounds (Real.exp O) (Real.exp O) (Real.exp O)
        ⟨Real.exp O, Real.exp_nonneg _⟩ (Real.exp (allocatedInactiveSupportLog D)) ∧
      ∀ (x : G → IntegerScalarCubeBox Empty S.value) (z : ℤ),
        ‖(((scale : ℝ) *
          (allocatedSupportedPhysicalGridPMF B U b hR hσ S q r hcell j i Finset.univ x
            (fun _ => z)).toReal : ℝ) : ℂ) - e.integerEval scale (fun _ => z)‖ ≤ 2 * ε := by
  dsimp only
  have hγ : principalProfileSize (R j)
      (layerIntegerPrincipalSlots (G := G) B j i).card ≤ 1 := by
    unfold principalProfileSize
    apply (div_le_one (by positivity)).mpr
    have hslots : (0 : ℝ) ≤ (layerIntegerPrincipalSlots (G := G) B j i).card := Nat.cast_nonneg _
    linarith only [hR1, hslots]
  have hrows (t : Finset Empty) (_ : t ∈ (Finset.univ : Finset (Finset Empty))) :
      t.card ≤ j.val + 1 := by
    have ht : t = ∅ := Subsingleton.elim _ _
    simp only [ht, Finset.card_empty]
    omega
  have hB' : uniformSpectrumBlockCount j.val
      (Finset.univ : Finset (Finset Empty)).card
      ((j.val + 1) * (Finset.univ : Finset (Finset Empty)).card) ≤
      Fintype.card (B ⟨j, Sum.inr i⟩) := by simpa using hB
  obtain ⟨e, he, herr⟩ := exists_allocated_inactive_fixed_support_site_expansion
    B U b S hR hσ (fun _ => (Finset.univ : Finset (Finset Empty)))
    j i q hq r hD (by simp) hP hp hv hPp hqv hε hε1 hE hεE
    (by simpa using hsize) hγ hsmall hcell hgrid hσ1 A hA hprimitive hrows hB'
  refine ⟨e, he, ?_⟩
  intro x z
  have hc (t : Finset Empty) : booleanCoefficient (fun _ : Finset Empty => z) t = z := by
    simp only [booleanCoefficient_const, (Subsingleton.elim t ∅ : t = ∅), ↓reduceIte]
  have hz := herr x (fun _ => z) (by
    intro t ht
    exact (ht (Finset.mem_univ t)).elim)
  simpa only [hc, Finset.card_univ, Fintype.card_finset, Fintype.card_empty, pow_zero,
    pow_one] using hz

theorem forecast_inactive_zero_axis_norm_le
    (j : Fin m) (i : Fin (n j)) (q : ℕ) (hq : 0 < q)
    [Nonempty (B ⟨j, Sum.inr i⟩)]
    (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option Empty → ZMod q)
    {D P p v : ℝ}
    (hD : AllocatedComparisonDimensions (G := G) B Empty
      (fun _ : Fin m => ((Finset.univ : Finset (Finset Empty)) : Type)) D)
    (hP : 1 ≤ P) (hp : 0 ≤ p) (hv : 0 ≤ v)
    (hPp : P ≤ Real.exp p) (hqv : (q : ℝ) ≤ Real.exp v)
    (hsize : q ≤ S.value) (hR1 : R j ≤ 1)
    (hsmall : basisAxisScale (b j) i ≤ S.value ^ (j.val + 1))
    (hcell : 0 < (principalTupleWeights (α := Empty) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
        (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
    (hgrid : allocatedGridAxis (I := I) U b S.value ⟨j, Sum.inr i⟩)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition)
    (hprimitive : scalarCubePrimitiveEnvelope Empty A 1 0 q ≤ P)
    (hB : uniformSpectrumBlockCount j.val 1 (j.val + 1) ≤ Fintype.card (B ⟨j, Sum.inr i⟩))
    (x : G → IntegerScalarCubeBox Empty S.value) (z : ℤ) :
    ‖(((allocatedPrincipalGridScale (G := G) B U b (R := R) j i : ℝ) *
      (allocatedSupportedPhysicalGridPMF B U b hR hσ S q r hcell j i Finset.univ x
        (fun _ => z)).toReal : ℝ) : ℂ)‖ ≤
      Real.exp (allocatedInactivePointCapLog m D p v) := by
  have hγ : principalProfileSize (R j)
      (layerIntegerPrincipalSlots (G := G) B j i).card ≤ 1 := by
    unfold principalProfileSize
    apply (div_le_one (by positivity)).mpr
    have hslots : (0 : ℝ) ≤ (layerIntegerPrincipalSlots (G := G) B j i).card := Nat.cast_nonneg _
    linarith only [hR1, hslots]
  have hrows (t : Finset Empty) (_ : t ∈ (Finset.univ : Finset (Finset Empty))) :
      t.card ≤ j.val + 1 := by
    have ht : t = ∅ := Subsingleton.elim _ _
    simp only [ht, Finset.card_empty]
    omega
  have hB' : uniformSpectrumBlockCount j.val
      (Finset.univ : Finset (Finset Empty)).card
      ((j.val + 1) * (Finset.univ : Finset (Finset Empty)).card) ≤
      Fintype.card (B ⟨j, Sum.inr i⟩) := by simpa using hB
  have hz := allocatedInactiveGrid_norm_exp_bound
    B U b S hR hσ (fun _ => (Finset.univ : Finset (Finset Empty)))
    j i q hq r hD (by simp) hP hp hv hPp hqv
    (by simpa using hsize) hγ hsmall hcell hgrid A hA hprimitive hrows hB' x (fun _ => z)
  simpa only [Finset.card_univ, Fintype.card_finset, Fintype.card_empty, pow_zero,
    pow_one] using hz

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {A : Type*} [Fintype A]

theorem exists_forecast_inactive_product_site
    (selected : A → Σ j : Fin m, Fin (n j))
    (hselected : Function.Injective selected)
    [∀ a, Nonempty (B ⟨(selected a).1, Sum.inr (selected a).2⟩)]
    (q : ℕ) (hq : 0 < q)
    (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option Empty → ZMod q)
    {D P p v δ E : ℝ}
    (hD : AllocatedComparisonDimensions (G := G) B Empty
      (fun _ : Fin m => ((Finset.univ : Finset (Finset Empty)) : Type)) D)
    (hP : 1 ≤ P) (hp : 0 ≤ p) (hv : 0 ≤ v)
    (hPp : P ≤ Real.exp p) (hqv : (q : ℝ) ≤ Real.exp v)
    (hδ : 0 < δ) (hE : 0 ≤ E)
    (hδE : δ⁻¹ ≤ Real.exp E)
    (hsize : q ≤ S.value) (hR1 : ∀ a, R (selected a).1 ≤ 1)
    (hsmall : ∀ a, basisAxisScale (b (selected a).1) (selected a).2 ≤
      S.value ^ ((selected a).1.val + 1))
    (hcell : 0 < (principalTupleWeights (α := Empty) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
        (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
    (hgrid : ∀ a, allocatedGridAxis (I := I) U b S.value
      ⟨(selected a).1, Sum.inr (selected a).2⟩)
    (hσ1 : ∀ a, σ (selected a).1 ≤ 1)
    (L : ℝ≥0) (hL : LipschitzWith L Real.smoothTransition)
    (hprimitive : scalarCubePrimitiveEnvelope Empty L 1 0 q ≤ P)
    (hB : ∀ a, uniformSpectrumBlockCount (selected a).1.val 1 ((selected a).1.val + 1) ≤
      Fintype.card (B ⟨(selected a).1, Sum.inr (selected a).2⟩)) :
    let scale := fun a => allocatedPrincipalGridScale (G := G) B U b (R := R)
      (selected a).1 (selected a).2
    let O := allocatedInactiveJointSiteLog m D p v E
    ∃ e : A → ScalarSiteExpansion.{0,0} (Finset Empty),
      (∀ a, (e a).Bounds (Real.exp O) (Real.exp O) (Real.exp O)
        ⟨Real.exp O, Real.exp_nonneg _⟩ (Real.exp (allocatedInactiveSupportLog D))) ∧
      ∀ (x : G → IntegerScalarCubeBox Empty S.value) (z : A → ℤ),
        ‖(((∏ a, (scale a : ℝ)) *
          (allocatedSupportedPhysicalJointPMF B U b hR hσ S q r hcell selected
            (fun _ => Finset.univ) x (fun a _ => z a)).toReal : ℝ) : ℂ) -
          siteFamilyEval e (fun _ => z) (fun _ a => (z a : ℝ) / scale a)‖ ≤ δ := by
  dsimp only
  let cap := Real.exp (allocatedInactivePointCapLog m D p v)
  let ε := uniformProductAccuracy (Fintype.card A) cap δ / 2
  obtain ⟨hτ, hτ1, _⟩ := uniformProductAccuracy_spec (Fintype.card A)
    (Real.exp_nonneg (allocatedInactivePointCapLog m D p v)) hδ
  have hε : 0 < ε := half_pos hτ
  have hε1 : ε ≤ 1 := by dsimp only [ε, cap]; linarith
  have hcount : (Fintype.card A : ℝ) ≤ D :=
    (Nat.cast_le.mpr (Fintype.card_le_of_injective selected hselected)).trans
      (allocatedIntegerAxes_card_le B (fun _ => (Finset.univ : Finset (Finset Empty))) hD)
  have hcapLog := allocatedInactivePointCapLog_nonneg m hD.nonneg hp hv
  have hτinv := uniformProductAccuracy_inverse_exp_bound (Fintype.card A)
    (Real.exp_nonneg _) hδ hD.nonneg hcapLog hE hcount (le_refl cap) hδE
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hεinv : ε⁻¹ ≤ Real.exp (allocatedInactiveJointAccuracyLog m D p v E) := by
    dsimp only [ε]
    rw [inv_div, div_eq_mul_inv]
    have hb := (mul_le_mul htwo hτinv (inv_nonneg.mpr hτ.le) (Real.exp_pos _).le).trans_eq
      (Real.exp_add _ _).symm
    exact hb.trans_eq (by unfold allocatedInactiveJointAccuracyLog; congr 1; ring)
  have hprecision := (allocatedInactiveJointLogs_nonneg m hD.nonneg hp hv hE).1
  have heach (a : A) := exists_forecast_inactive_zero_axis_site B U b S hR hσ
    (selected a).1 (selected a).2 q hq r hD hP hp hv hPp hqv hε hε1 hprecision
    hεinv hsize (hR1 a) (hsmall a) hcell (hgrid a) (hσ1 a) L hL hprimitive (hB a)
  choose e he herr using heach
  refine ⟨e, he, ?_⟩
  intro x z
  let scale := fun a => allocatedPrincipalGridScale (G := G) B U b (R := R)
    (selected a).1 (selected a).2
  let g (a : A) : ℂ := (((scale a : ℝ) *
    (allocatedSupportedPhysicalGridPMF B U b hR hσ S q r hcell
      (selected a).1 (selected a).2 Finset.univ x (fun _ => z a)).toReal : ℝ) : ℂ)
  have hg (a : A) : ‖g a‖ ≤ cap := forecast_inactive_zero_axis_norm_le
    B U b S hR hσ (selected a).1 (selected a).2 q hq r hD hP hp hv hPp hqv
    hsize (hR1 a) (hsmall a) hcell (hgrid a) L hL hprimitive (hB a) x (z a)
  have herr' (a : A) :
      ‖g a - (e a).eval (fun _ => z a) (fun _ => (z a : ℝ) / scale a)‖ ≤
      uniformProductAccuracy (Fintype.card A) cap δ := by
    simpa only [ScalarSiteExpansion.integerEval, ε, mul_div_cancel₀ _ (by norm_num : (2:ℝ) ≠ 0)]
      using herr a x (z a)
  have hp' := siteFamily_approximation e (fun _ => z)
    (fun _ a => (z a : ℝ) / scale a) g (Fintype.card A) le_rfl
    (Real.exp_nonneg _) hδ hg herr'
  have hj : (((∏ a, (scale a : ℝ)) *
      (allocatedSupportedPhysicalJointPMF B U b hR hσ S q r hcell selected
        (fun _ => Finset.univ) x (fun a _ => z a)).toReal : ℝ) : ℂ) = ∏ a, g a := by
    rw [allocatedSupportedPhysicalGrid_joint_mass B U b hR hσ S q r hcell
      selected (fun _ => Finset.univ) x hselected hgrid _, ← Finset.prod_mul_distrib,
      Complex.ofReal_prod]
  rw [hj]
  exact hp'

end Erdos3.VectorPolynomial

end

end OAI
