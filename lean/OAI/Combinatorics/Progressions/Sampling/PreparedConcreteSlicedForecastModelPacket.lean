import OAI.Combinatorics.Progressions.Sampling.AllocatedExternalCandidateActualShearForecastScore

namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {X₀ J₀ : Type} {m : ℕ} (L : RankPreparationFamily X₀ J₀ m) (Jalloc : ℕ)
variable (U : ∀ j : Fin m, Submodule ℝ (RankPreparationLayer.Coord (L j) → ℝ))
variable (b : ∀ j, Basis (Fin (preparedSamplerTransverse L j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (o : ∀ j, OrthonormalBasis (PreparedSamplerContinuous L j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ}
variable (S : LayerSamplerScale (J := fun j => RankPreparationLayer.Coord (L j))
  (G := EnlargedPreparedCommonKernel m Jalloc)
  (EnlargedPreparedCommonSamplerBlock L Jalloc) U b R σ)
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable (bW : ∀ j, Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (RankPreparationLayer.Coord (L j)))
    (euclideanSubspace (U j))))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable [∀ j, IsZLattice ℝ (latticeSection
  (standardEuclideanLattice (RankPreparationLayer.Coord (L j))) (euclideanSubspace (U j)))]

variable {M nX : ℕ}
variable (hm : 0 < m) (hCoord : ∀ j, Fintype.card (L j).Coord ≤ M)
variable {pRadius gainLog Qstride PF Pchart cost : ℝ} (Pdim : ℝ)
variable (hpRadius : 0 ≤ pRadius) (hGain : 0 ≤ gainLog)
variable (hQstride : 0 ≤ Qstride) (hPF : 0 ≤ PF) (hChart : 0 ≤ Pchart)
variable (hcost : 0 ≤ cost)
variable (hratio : ∀ j, mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ Real.exp Pchart)
variable (hR : ∀ j, 0 < R j) (hRone : ∀ j, R j ≤ 1)
variable (hRinv : ∀ j, (R j)⁻¹ ≤ Real.exp pRadius) (hσone : ∀ j, σ j ≤ 1)
variable (forward : Fin m → ℝ≥0)
variable (hforward : ∀ j, ∀ w : EuclideanSpace ℝ (RankPreparationLayer.Coord (L j)),
  ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) w‖ ≤ forward j * ‖w‖)
variable (hforwardBound : ∀ j, (forward j : ℝ) ≤ Real.exp PF)
variable (radius : ℝ≥0) (T : Fin m → ℝ)
variable (hT : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent
  (LayerSamplerVariables (EnlargedPreparedCommonKernel m Jalloc)
    (PreparedSamplerContinuous L) (preparedSamplerTransverse L)
    (EnlargedPreparedCommonSamplerBlock L Jalloc)) (j.val + 1)) : ℝ) *
  (2 * 2 ^ (j.val + 1)) ≤ T j)
variable (hradius : ∀ j : Fin m,
  (boundedBooleanJetRows (Fin 1) (j.val + 1)).card * T j ≤ (radius : ℝ))
variable (inverse : Fin m → ℝ) (hinverse : ∀ j, 0 ≤ inverse j)
variable (hchart : ∀ j
  (w : euclideanSubspace (U j) × (Fin (preparedSamplerTransverse L j) → ℝ)),
  ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm w‖ ≤ inverse j * ‖w‖)
variable (hsourceBudget : ∀ j : Fin m,
  ((boundedBooleanJetRows (Fin 1) (j.val + 1)).card + 1 : ℝ) *
    (Fintype.card (Finset (Fin 1)) : ℝ) *
    (inverse j * (((Fintype.card ((PreparedSamplerContinuous L) j) : ℝ) + 1) *
      (2 * (radius : ℝ) * R j))) ≤ 1 / 4)

variable {hσ : ∀ j, 0 < σ j} {Lrank : ℕ}
variable {spatial : Fin Lrank ↪ EnlargedPreparedCommonKernel m Jalloc}
variable {kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪
  EnlargedPreparedCommonKernel m Jalloc}
variable {block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := PreparedSamplerContinuous L) U b S.value) j,
  Fin Lrank ↪ EnlargedPreparedCommonSamplerBlock L Jalloc ⟨j, a.val⟩}
variable {Tsp : Type} [Fintype Tsp]
variable {spatialEquiv : EnlargedPreparedCommonKernel m Jalloc ≃ Fin nX ⊕ (Fin nX ⊕ Tsp)}
variable {Wsp Lsp : ℝ} {physicalN : Fin nX → ℕ}
variable (originalpoly : ∀ j, VectorPolynomial (Fin nX) ℝ (RankPreparationLayer.Coord (L j) → ℝ))
variable (hmem : ∀ j d, coefficients (originalpoly j) d ∈ U j)

theorem exists_preparedConcreteSlicedForecastModelPacket_from_primitive_bounds
    (δ : ℝ) (Hchild : ℕ) (kernelV Ptail pSite w vchild : ℝ)
    (hδ : 0 < δ) (hk : 0 ≤ kernelV) (hPtail : 1 ≤ Ptail)
    (hprimitive : max 1 (scalarCubePrimitiveEnvelope Empty scalarSourceTransitionBound 1 0 1) ≤ Ptail)
    (hpSite : 0 ≤ pSite) (hw : 0 ≤ w) (hvc : 0 ≤ vchild)
    (hPp : Ptail ≤ Real.exp pSite) (hδw : δ⁻¹ ≤ Real.exp w)
    (hchild : (Hchild : ℝ) ≤ Real.exp vchild)
    (u p : ℝ) (hu : 0 ≤ u) (hp : 0 ≤ p)
    (hCapLog : preparedSlicedForecastCapLog m M nX Jalloc
      Pdim cost pRadius gainLog Qstride Pchart kernelV pSite w vchild ≤ p) :
    let s := preparedActualSlicedForecastSetup (nX := nX) L Jalloc U b o S bW hb hm hCoord Pdim
      hpRadius hGain hQstride hPF hChart hcost hratio hR hRone hRinv hσone
      forward hforward hforwardBound radius T hT hradius inverse hinverse hchart hsourceBudget
    ∃ qEarly : ActualFixedSpatialSlicedForecastNumerics s,
      qEarly.δ = δ ∧ qEarly.Hchild = Hchild ∧ qEarly.v = kernelV ∧ qEarly.Ptail = Ptail ∧
      qEarly.E = 2 * u + 4 * p + 12 ∧
      qEarly.capLog = preparedSlicedForecastCapLog m M nX Jalloc
        Pdim cost pRadius gainLog Qstride Pchart kernelV pSite w vchild ∧
      qEarly.capLog ≤ p ∧ 0 ≤ qEarly.massLog ∧ 0 ≤ qEarly.capLog ∧
      PreparedActualSlicedForecastModelPacket
        (hR := hR) (hσ := hσ) (spatial := spatial) (kernel := kernel) (block := block)
        (spatialEquiv := spatialEquiv) (Wsp := Wsp) (Lsp := Lsp) (physicalN := physicalN)
        s qEarly o bW hb originalpoly hmem u p (Real.exp p) := by
  intro s
  obtain ⟨hP, hscale, hbad, hpres, hκ, _, hprimitiveEq⟩ :=
    preparedActualSlicedForecastSetup_scalar_values (nX := nX) L Jalloc U b o S bW hb hm hCoord Pdim
      hpRadius hGain hQstride hPF hChart hcost hratio hR hRone hRinv hσone
      forward hforward hforwardBound radius T hT hradius inverse hinverse hchart hsourceBudget
  change s.P = _ at hP
  change s.Pscale = _ at hscale
  change s.Pbad = _ at hbad
  change s.Ppres = _ at hpres
  change s.Pκ = _ at hκ
  change s.Pcap = _ at hprimitiveEq
  have hprimitive' : s.Pcap ≤ Ptail := hprimitiveEq.trans_le hprimitive
  have hCapLog' : actualSlicedForecastModelCapLog m (nX + m * M) (Fintype.card (Fin nX))
      s.P s.Pscale s.Pbad s.Ppres s.Pκ kernelV pSite w vchild ≤ p := by
    simpa only [hP, hscale, hbad, hpres, hκ, Fintype.card_fin,
      preparedSlicedForecastCapLog] using hCapLog
  have hresult := exists_preparedActualSlicedForecastModelPacket_from_setup_with_cap_bound
    (hR := hR) (hσ := hσ) (spatial := spatial) (kernel := kernel) (block := block)
    (spatialEquiv := spatialEquiv) (Wsp := Wsp) (Lsp := Lsp) (physicalN := physicalN)
    s o bW hb originalpoly hmem δ Hchild kernelV Ptail pSite w vchild
    hδ hk hPtail hprimitive' hpSite hw hvc hPp hδw hchild u p hu hp hCapLog'
  simpa only [hP, hscale, hbad, hpres, hκ, Fintype.card_fin,
    preparedSlicedForecastCapLog] using hresult

theorem exists_preparedConcreteSlicedForecastModelPacket
    (childLog u p : ℝ) (hchildLog : 0 ≤ childLog) (hu : 0 ≤ u) (hp : 0 ≤ p)
    (hCapLog : preparedConcreteSlicedForecastCapLog m M nX Jalloc
      Pdim cost pRadius gainLog Qstride Pchart childLog ≤ p) :
    let s := preparedActualSlicedForecastSetup (nX := nX) L Jalloc U b o S bW hb hm hCoord Pdim
      hpRadius hGain hQstride hPF hChart hcost hratio hR hRone hRinv hσone
      forward hforward hforwardBound radius T hT hradius inverse hinverse hchart hsourceBudget
    ∃ qEarly : ActualFixedSpatialSlicedForecastNumerics s,
      qEarly.δ = preparedSlicedForecastDensity cost ∧
      qEarly.Hchild = preparedSlicedForecastChildSize childLog ∧ qEarly.v = cost + 1 ∧
      qEarly.Ptail = preparedSlicedForecastTailCap cost ∧
      qEarly.E = 2 * u + 4 * p + 12 ∧
      qEarly.Pnative = preparedConcreteSlicedForecastNativeLog m M nX Jalloc
        Pdim cost pRadius gainLog Qstride PF Pchart childLog (2 * u + 4 * p + 12) ∧
      qEarly.massLog = preparedConcreteSlicedForecastMassLog m M nX Jalloc
        Pdim cost pRadius gainLog Qstride Pchart childLog (2 * u + 4 * p + 12) ∧
      qEarly.capLog = preparedConcreteSlicedForecastCapLog m M nX Jalloc
        Pdim cost pRadius gainLog Qstride Pchart childLog ∧
      qEarly.Ctail = Real.exp (preparedConcreteSlicedForecastTailSiteLog m M nX Jalloc
        Pdim cost pRadius childLog) ∧
      (qEarly.T : ℝ) ≤ Real.exp (preparedConcreteSlicedForecastPeriodLog m M nX Jalloc
        Pdim cost pRadius gainLog Qstride Pchart childLog (2 * u + 4 * p + 12)) ∧
      qEarly.capLog ≤ p ∧ 0 ≤ qEarly.massLog ∧ 0 ≤ qEarly.capLog ∧ 0 ≤ qEarly.Pnative ∧
      PreparedActualSlicedForecastModelPacket
        (hR := hR) (hσ := hσ) (spatial := spatial) (kernel := kernel) (block := block)
        (spatialEquiv := spatialEquiv) (Wsp := Wsp) (Lsp := Lsp) (physicalN := physicalN)
        s qEarly o bW hb originalpoly hmem u p (Real.exp p) := by
  intro s
  obtain ⟨qEarly, hqδ, hqH, hqv, hqP, hqE, hqNative, hqMass, hqCap,
      hqTail, hqPeriod, hqMass0, hqCap0, hqNative0⟩ :=
    preparedConcreteSlicedForecastEarlyLogs (nX := nX) L Jalloc U b o S bW hb hm hCoord Pdim
      hpRadius hGain hQstride hPF hChart hcost hratio hR hRone hRinv hσone
      forward hforward hforwardBound radius T hT hradius inverse hinverse hchart hsourceBudget
      childLog (2 * u + 4 * p + 12) hchildLog (by positivity)
  have hqCapP : qEarly.capLog ≤ p := hqCap.trans_le hCapLog
  refine ⟨qEarly, hqδ, hqH, hqv, hqP, hqE, hqNative, hqMass, hqCap,
    hqTail, hqPeriod, hqCapP, hqMass0, hqCap0, hqNative0, ?_⟩
  exact exists_preparedActualSlicedForecastModelPacket
    (hR := hR) (hσ := hσ) (spatial := spatial) (kernel := kernel) (block := block)
    (spatialEquiv := spatialEquiv) (Wsp := Wsp) (Lsp := Lsp) (physicalN := physicalN)
    s qEarly o bW hb originalpoly hmem u p (Real.exp p) hqE.ge
    (Real.exp_le_exp.mpr hqCapP)

end Erdos3.VectorPolynomial

end

end OAI
