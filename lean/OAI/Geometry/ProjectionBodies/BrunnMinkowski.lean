import OAI.Geometry.ProjectionBodies.SliceTransport

namespace OAI

universe uE uF

noncomputable section
open Set MeasureTheory Filter Topology
open scoped Pointwise
namespace PettyProjection
section
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
    [Measure.IsAddHaarMeasure (volume : Measure E)]

/-- The dimension-induction predicate, used only with a proved lower-dimensional
case. It is not an extra hypothesis on the projection-volume main theorem. -/
def BrunnMinkowskiRoot (E : Type uE) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasureSpace E] (m : ℕ) : Prop :=
  ∀ K M : Set E, IsCompact K → Convex ℝ K → (interior K).Nonempty →
    IsCompact M → Convex ℝ M → (interior M).Nonempty →
    ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a+b=1 →
      a*(volume.real K)^((m:ℝ)⁻¹)+b*(volume.real M)^((m:ℝ)⁻¹) ≤
        (volume.real (a • K+b • M))^((m:ℝ)⁻¹)

omit [FiniteDimensional ℝ E] [BorelSpace E] in
lemma sliceDensity_root_concave {m : ℕ} (hm : BrunnMinkowskiRoot E m)
    {K : Set (E × ℝ)} (hK : IsCompact K) (hc : Convex ℝ K)
    (hi : (interior K).Nonempty) {l r : ℝ}
    (hl : l ∈ Prod.snd '' K) (hr : r ∈ Prod.snd '' K) :
    ConcaveOn ℝ (Ioo l r) (fun s => (sliceDensity K s)^((m:ℝ)⁻¹)) := by
  refine ⟨convex_Ioo l r,?_⟩
  intro s hs t ht a b ha hb hab
  have hlower := hm (horizontalSlice K s) (horizontalSlice K t)
    (horizontalSlice_compact hK s) (horizontalSlice_convex hc s)
    (horizontalSlice_interior_nonempty hc hi hl hr hs)
    (horizontalSlice_compact hK t) (horizontalSlice_convex hc t)
    (horizontalSlice_interior_nonempty hc hi hl hr ht) a b ha hb hab
  exact hlower.trans (Real.rpow_le_rpow measureReal_nonneg
    (measureReal_mono (horizontalSlice_combo_subset hc ha hb hab s t)
      (horizontalSlice_compact hK (a*s+b*t)).measure_ne_top) (by positivity))

omit [FiniteDimensional ℝ E] [BorelSpace E] in
lemma sliceDensity_continuous {m : ℕ} (hm0 : 0 < m) (hm : BrunnMinkowskiRoot E m)
    {K : Set (E × ℝ)} (hK : IsCompact K) (hc : Convex ℝ K)
    (hi : (interior K).Nonempty) {l r : ℝ}
    (hl : l ∈ Prod.snd '' K) (hr : r ∈ Prod.snd '' K) :
    ContinuousOn (sliceDensity K) (Ioo l r) := by
  have h := (ConcaveOn.continuousOn isOpen_Ioo
    (sliceDensity_root_concave hm hK hc hi hl hr)).pow m
  convert h using 1
  funext s
  exact (Real.rpow_inv_natCast_pow (sliceDensity_nonneg K s) hm0.ne').symm

/-- The actual convex-body product step, not a replacement by abstract densities. -/
theorem brunnMinkowski_product_unit {m : ℕ} (hm0 : 0 < m) (hm : BrunnMinkowskiRoot E m)
    {K M : Set (E × ℝ)} (hK : IsCompact K) (hcK : Convex ℝ K)
    (hiK : (interior K).Nonempty) (hM : IsCompact M) (hcM : Convex ℝ M)
    (hiM : (interior M).Nonempty) (hvK : volume.real K=1) (hvM : volume.real M=1)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a+b=1) :
    1 ≤ volume.real (a • K+b • M) := by
  obtain ⟨l,r,hlr,hpr⟩ := vertical_projection_interval hK hcK hiK
  obtain ⟨L,R,hLR,hPR⟩ := vertical_projection_interval hM hcM hiM
  have hl : l ∈ Prod.snd '' K := by rw [hpr]; exact left_mem_Icc.mpr hlr.le
  have hr : r ∈ Prod.snd '' K := by rw [hpr]; exact right_mem_Icc.mpr hlr.le
  have hL : L ∈ Prod.snd '' M := by rw [hPR]; exact left_mem_Icc.mpr hLR.le
  have hR : R ∈ Prod.snd '' M := by rw [hPR]; exact right_mem_Icc.mpr hLR.le
  have hC : IsCompact (a • K+b • M) := (hK.smul a).add (hM.smul b)
  have hbounds : Prod.snd '' (a • K+b • M) ⊆ Icc (a*l+b*L) (a*r+b*R) := by
    rintro s ⟨_,⟨_,⟨x,hx,rfl⟩,_,⟨y,hy,rfl⟩,rfl⟩,rfl⟩
    have hx' : x.2 ∈ Icc l r := by rw [← hpr]; exact mem_image_of_mem _ hx
    have hy' : y.2 ∈ Icc L R := by rw [← hPR]; exact mem_image_of_mem _ hy
    change a*l+b*L ≤ a*x.2+b*y.2 ∧ a*x.2+b*y.2 ≤ a*r+b*R
    exact ⟨add_le_add (mul_le_mul_of_nonneg_left hx'.1 ha.le) (mul_le_mul_of_nonneg_left hy'.1 hb.le),
      add_le_add (mul_le_mul_of_nonneg_left hx'.2 ha.le) (mul_le_mul_of_nonneg_left hy'.2 hb.le)⟩
  rw [← sliceDensity_interval_integral hC (by nlinarith) hbounds]
  apply slice_transport hm0 ha hb hab hlr hLR
    (sliceDensity_continuous hm0 hm hK hcK hiK hl hr)
    (sliceDensity_continuous hm0 hm hM hcM hiM hL hR)
    (sliceDensity_integrable hK).intervalIntegrable
    (sliceDensity_integrable hM).intervalIntegrable
    (fun s hs => sliceDensity_pos hK hcK hiK hl hr hs)
    (fun s hs => sliceDensity_pos hM hcM hiM hL hR hs)
  · rw [sliceDensity_interval_integral hK hlr.le (by rw [hpr]),hvK]
  · rw [sliceDensity_interval_integral hM hLR.le (by rw [hPR]),hvM]
  · exact (sliceDensity_integrable hC).intervalIntegrable
  · intro s hs t ht
    have hroot := hm (horizontalSlice K s) (horizontalSlice M t)
      (horizontalSlice_compact hK s) (horizontalSlice_convex hcK s)
      (horizontalSlice_interior_nonempty hcK hiK hl hr hs)
      (horizontalSlice_compact hM t) (horizontalSlice_convex hcM t)
      (horizontalSlice_interior_nonempty hcM hiM hL hR ht) a b ha.le hb.le hab
    have hf0 := sliceDensity_nonneg K s
    have hg0 := sliceDensity_nonneg M t
    have hroot' := pow_le_pow_left₀ (by positivity : 0 ≤ a*(sliceDensity K s)^((m:ℝ)⁻¹)+b*(sliceDensity M t)^((m:ℝ)⁻¹)) hroot m
    rw [Real.rpow_inv_natCast_pow measureReal_nonneg hm0.ne'] at hroot'
    exact hroot'.trans (measureReal_mono (horizontalSlice_minkowski_subset K M a b s t)
      (horizontalSlice_compact hC _).measure_ne_top)

end
end PettyProjection
end

noncomputable section
open Set MeasureTheory Filter Topology
open scoped Pointwise
namespace PettyProjection
section
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
    [Measure.IsAddHaarMeasure (volume : Measure E)]

lemma volumeReal_smul_nonneg {r : ℝ} (hr : 0 ≤ r) (K : Set E) :
    volume.real (r • K)=r^(Module.finrank ℝ E)*volume.real K := by
  rw [Measure.real,Measure.addHaar_smul_of_nonneg volume hr,ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (pow_nonneg hr _)]
  rfl

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
lemma volumeReal_pos_of_body {K : Set E} (hK : IsCompact K) (hi : (interior K).Nonempty) :
    0 < volume.real K :=
  ENNReal.toReal_pos (ne_of_gt (lt_of_lt_of_le (isOpen_interior.measure_pos volume hi)
    (measure_mono interior_subset))) hK.measure_ne_top

/-- Usual normalization from the unit-volume form. The exponent is the actual
finite dimension of the Haar space, and the bodies remain arbitrary. -/
theorem brunnMinkowski_of_unit {d : ℕ} (hd : 0 < d) (hDim : Module.finrank ℝ E=d)
    (hunit : ∀ K M : Set E, IsCompact K → Convex ℝ K → (interior K).Nonempty →
      IsCompact M → Convex ℝ M → (interior M).Nonempty →
      volume.real K=1 → volume.real M=1 → ∀ a b : ℝ, 0 < a → 0 < b → a+b=1 →
      1 ≤ volume.real (a • K+b • M)) : BrunnMinkowskiRoot E d := by
  intro K M hK hcK hiK hM hcM hiM a b ha hb hab
  obtain rfl | ha := ha.eq_or_lt
  · have hb1 : b=1 := by linarith
    simp [hb1,zero_smul_set (hiK.mono interior_subset)]
  obtain rfl | hb := hb.eq_or_lt
  · have ha1 : a=1 := by linarith
    simp [ha1,zero_smul_set (hiM.mono interior_subset)]
  let p := (volume.real K)^((d:ℝ)⁻¹)
  let q := (volume.real M)^((d:ℝ)⁻¹)
  let D := a*p+b*q
  have hp : 0 < p := Real.rpow_pos_of_pos (volumeReal_pos_of_body hK hiK) _
  have hq : 0 < q := Real.rpow_pos_of_pos (volumeReal_pos_of_body hM hiM) _
  have hD : 0 < D := by dsimp [D]; positivity
  have hpm : p^d=volume.real K := Real.rpow_inv_natCast_pow measureReal_nonneg hd.ne'
  have hqm : q^d=volume.real M := Real.rpow_inv_natCast_pow measureReal_nonneg hd.ne'
  have hUK : volume.real (p⁻¹ • K)=1 := by
    rw [volumeReal_smul_nonneg (inv_nonneg.mpr hp.le),hDim,inv_pow,hpm]
    exact inv_mul_cancel₀ (volumeReal_pos_of_body hK hiK).ne'
  have hUM : volume.real (q⁻¹ • M)=1 := by
    rw [volumeReal_smul_nonneg (inv_nonneg.mpr hq.le),hDim,inv_pow,hqm]
    exact inv_mul_cancel₀ (volumeReal_pos_of_body hM hiM).ne'
  have hiUK : (interior (p⁻¹ • K)).Nonempty := by
    rw [interior_smul₀ (inv_ne_zero hp.ne')]
    exact hiK.image _
  have hiUM : (interior (q⁻¹ • M)).Nonempty := by
    rw [interior_smul₀ (inv_ne_zero hq.ne')]
    exact hiM.image _
  have he := hunit (p⁻¹ • K) (q⁻¹ • M) (hK.smul _) (hcK.smul _) hiUK
    (hM.smul _) (hcM.smul _) hiUM hUK hUM (a*p/D) (b*q/D)
    (by positivity) (by positivity) (by rw [← add_div]; exact div_self hD.ne')
  have hsets : (a*p/D) • (p⁻¹ • K)+(b*q/D) • (q⁻¹ • M)=D⁻¹ • (a • K+b • M) := by
    rw [smul_add,smul_smul,smul_smul,smul_smul,smul_smul]
    congr 2 <;> field_simp
  rw [hsets,volumeReal_smul_nonneg (inv_nonneg.mpr hD.le),hDim,inv_pow] at he
  have hpow : D^d ≤ volume.real (a • K+b • M) := by
    have hx := mul_le_mul_of_nonneg_left he (pow_nonneg hD.le d)
    simpa only [mul_one,← mul_assoc,mul_inv_cancel₀ (pow_ne_zero _ hD.ne'),one_mul] using hx
  have hr := Real.rpow_le_rpow (pow_nonneg hD.le d) hpow (by positivity : 0 ≤ (d:ℝ)⁻¹)
  rw [← Real.rpow_natCast,← Real.rpow_mul hD.le,mul_inv_cancel₀ (by exact_mod_cast hd.ne'),Real.rpow_one] at hr
  exact hr

end
end PettyProjection
end

noncomputable section
open Set MeasureTheory Filter Topology
open scoped Pointwise
namespace PettyProjection
section
variable {E : Type uE} {F : Type uF} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [MeasureSpace E] [BorelSpace E] [MeasureSpace F] [BorelSpace F]

omit [MeasureSpace E] [BorelSpace E] [MeasureSpace F] [BorelSpace F] in
lemma linearEquiv_preimage_combo (e : E ≃L[ℝ] F) (K M : Set F) (a b : ℝ) :
    e ⁻¹' (a • K+b • M)=a • (e ⁻¹' K)+b • (e ⁻¹' M) := by
  ext z
  constructor
  · rintro ⟨_,⟨x,hx,rfl⟩,_,⟨y,hy,rfl⟩,he⟩
    refine ⟨a • e.symm x,⟨e.symm x,by simpa using hx,rfl⟩,
      b • e.symm y,⟨e.symm y,by simpa using hy,rfl⟩,?_⟩
    apply e.injective
    simpa using he
  · rintro ⟨_,⟨x,hx,rfl⟩,_,⟨y,hy,rfl⟩,rfl⟩
    exact ⟨a • e x,⟨e x,hx,rfl⟩,b • e y,⟨e y,hy,rfl⟩,by simp⟩

omit [BorelSpace E] in
lemma BrunnMinkowskiRoot.equiv {m : ℕ} (hm : BrunnMinkowskiRoot E m)
    (e : E ≃L[ℝ] F) (he : MeasurePreserving e) : BrunnMinkowskiRoot F m := by
  intro K M hK hcK hiK hM hcM hiM a b ha hb hab
  have hPK : IsCompact (e ⁻¹' K) := e.toHomeomorph.isCompact_preimage.mpr hK
  have hPM : IsCompact (e ⁻¹' M) := e.toHomeomorph.isCompact_preimage.mpr hM
  have hiPK : (interior (e ⁻¹' K)).Nonempty := by
    change (interior (e.toHomeomorph ⁻¹' K)).Nonempty
    rw [← e.toHomeomorph.preimage_interior]
    obtain ⟨x,hx⟩ := hiK
    exact ⟨e.symm x,by simpa using hx⟩
  have hiPM : (interior (e ⁻¹' M)).Nonempty := by
    change (interior (e.toHomeomorph ⁻¹' M)).Nonempty
    rw [← e.toHomeomorph.preimage_interior]
    obtain ⟨x,hx⟩ := hiM
    exact ⟨e.symm x,by simpa using hx⟩
  have h := hm (e ⁻¹' K) (e ⁻¹' M) hPK (hcK.linear_preimage e.toLinearMap) hiPK
    hPM (hcM.linear_preimage e.toLinearMap) hiPM a b ha hb hab
  have hm' (S : Set F) (hS : IsCompact S) : volume.real (e ⁻¹' S)=volume.real S :=
    congrArg ENNReal.toReal (he.measure_preimage hS.measurableSet.nullMeasurableSet)
  rw [hm' K hK,hm' M hM,← linearEquiv_preimage_combo,hm' _ ((hK.smul _).add (hM.smul _))] at h
  exact h
end

/-- The one-dimensional base case, with no symmetry or origin condition. -/
lemma brunnMinkowski_real : BrunnMinkowskiRoot ℝ 1 := by
  intro K M hK hcK hiK hM hcM hiM a b ha hb hab
  obtain rfl | ha := ha.eq_or_lt
  · have hb1 : b=1 := by linarith
    simp [hb1,zero_smul_set (hiK.mono interior_subset)]
  obtain rfl | hb := hb.eq_or_lt
  · have ha1 : a=1 := by linarith
    simp [ha1,zero_smul_set (hiM.mono interior_subset)]
  rw [compact_convex_real_interval hK hcK (hiK.mono interior_subset),
    compact_convex_real_interval hM hcM (hiM.mono interior_subset)]
  have hKlr : sInf K ≤ sSup K := (hK.isGLB_sInf (hiK.mono interior_subset)).1
    (hK.sSup_mem (hiK.mono interior_subset))
  have hMlr : sInf M ≤ sSup M := (hM.isGLB_sInf (hiM.mono interior_subset)).1
    (hM.sSup_mem (hiM.mono interior_subset))
  have hKa : a*sInf K ≤ a*sSup K := mul_le_mul_of_nonneg_left hKlr ha.le
  have hMb : b*sInf M ≤ b*sSup M := mul_le_mul_of_nonneg_left hMlr hb.le
  rw [LinearOrderedField.smul_Icc ha,LinearOrderedField.smul_Icc hb,Icc_add_Icc hKa hMb]
  simp only [Nat.cast_one,inv_one,Real.rpow_one,Real.volume_real_Icc]
  rw [max_eq_left (sub_nonneg.mpr hKlr),max_eq_left (sub_nonneg.mpr hMlr),
    max_eq_left (sub_nonneg.mpr (add_le_add hKa hMb))]
  nlinarith

/-- Standard coordinate splitting, with explicit measure evidence. -/
def finSplitLinear (n : ℕ) : (Fin (n+1) → ℝ) ≃ₗ[ℝ] ((Fin n → ℝ) × ℝ) where
  toEquiv := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0).toEquiv.trans
    (Equiv.prodComm _ _)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def finSplit (n : ℕ) : (Fin (n+1) → ℝ) ≃L[ℝ] ((Fin n → ℝ) × ℝ) :=
  (finSplitLinear n).toContinuousLinearEquiv

lemma finSplit_measurePreserving (n : ℕ) : MeasurePreserving (finSplit n) := by
  have hs : MeasurePreserving (Prod.swap : ℝ × (Fin n → ℝ) → (Fin n → ℝ) × ℝ) := by
    simpa only [Measure.volume_eq_prod] using
      (Measure.measurePreserving_swap (μ := (volume : Measure ℝ)) (ν := (volume : Measure (Fin n → ℝ))))
  exact hs.comp (volume_preserving_piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0)

def finOneLinear : (Fin 1 → ℝ) ≃ₗ[ℝ] ℝ := LinearEquiv.funUnique (Fin 1) ℝ ℝ

def finOne : (Fin 1 → ℝ) ≃L[ℝ] ℝ := finOneLinear.toContinuousLinearEquiv

lemma finOne_measurePreserving : MeasurePreserving finOne :=
  volume_preserving_piUnique (fun _ : Fin 1 => ℝ)

/-- Brunn--Minkowski in all positive Cartesian dimensions, obtained by the
actual convex-body slice induction. -/
theorem brunnMinkowski_fin (n : ℕ) : BrunnMinkowskiRoot (Fin (n+1) → ℝ) (n+1) := by
  induction n with
  | zero =>
    exact brunnMinkowski_real.equiv finOne.symm
      (MeasurePreserving.symm finOne.toHomeomorph.toMeasurableEquiv finOne_measurePreserving)
  | succ n ih =>
    let : Measure.IsAddHaarMeasure (volume : Measure ((Fin (n+1) → ℝ) × ℝ)) := by
      rw [Measure.volume_eq_prod]
      infer_instance
    have hprod : BrunnMinkowskiRoot ((Fin (n+1) → ℝ) × ℝ) (n+1+1) := by
      apply brunnMinkowski_of_unit (by omega)
      · simp
      · intro K M hK hcK hiK hM hcM hiM hvK hvM a b ha hb hab
        exact brunnMinkowski_product_unit (by omega) ih hK hcK hiK hM hcM hiM hvK hvM ha hb hab
    exact hprod.equiv (finSplit (n+1)).symm
      (MeasurePreserving.symm (finSplit (n+1)).toHomeomorph.toMeasurableEquiv
        (finSplit_measurePreserving (n+1)))

/-- Standard Euclidean volume version used for the projection-body theorem. -/
theorem brunnMinkowski_space {n : ℕ} (hn : 0 < n) : BrunnMinkowskiRoot (Space n) n := by
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  exact (brunnMinkowski_fin m).equiv
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (m+1) => ℝ)).symm
    (PiLp.volume_preserving_toLp (Fin (m+1)))

end PettyProjection
end

noncomputable section
open Set MeasureTheory Filter Topology
namespace PettyProjection

/-- Brunn--Minkowski for the canonical Euclidean volume on any finite-dimensional
real inner-product space. -/
theorem brunnMinkowski_innerProduct {E : Type uE} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (hE : 0 < Module.finrank ℝ E) : BrunnMinkowskiRoot E (Module.finrank ℝ E) := by
  exact (brunnMinkowski_space hE).equiv
    (stdOrthonormalBasis ℝ E).repr.symm.toContinuousLinearEquiv
    (stdOrthonormalBasis ℝ E).measurePreserving_repr_symm

end PettyProjection
end

end OAI
