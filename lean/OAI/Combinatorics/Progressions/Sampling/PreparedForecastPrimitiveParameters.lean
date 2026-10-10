import OAI.Combinatorics.Progressions.Sampling.ActualForecastModelPrecision

namespace OAI

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Classical NNReal

theorem exists_preparedForecastPrimitiveParameters
    {m : ℕ} (Dmod d : ℕ)
    {G X Z : Type*} [Fintype G] [Fintype X] [Fintype Z]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    (R σ : Fin m → ℝ) (s : Empty ↪ Z)
    {P δslice : ℝ} (hP : 1 ≤ P) (hδslice : 0 < δslice)
    (hδsliceInv : δslice⁻¹ ≤ Real.exp P)
    (hX : (Fintype.card X : ℝ) ≤ P) (hZ : (Fintype.card Z : ℝ) ≤ P)
    (hblocks : (∑ a, (Fintype.card (B a) : ℝ)) ≤ P)
    (hprofile : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P)
    (forward : Fin m → ℝ≥0) (K r : ℝ≥0)
    {D pcap Pscale Pbad Ppres E Pτ PK PF τ : ℝ}
    (hD : 0 ≤ D) (hDP : D ≤ P)
    (haxes : (Fintype.card (LayerSamplerAxis I n) : ℝ) ≤ D)
    (hdim : ((∑ j, Fintype.card (J j) : ℕ) : ℝ) ≤ D)
    (hpcap : 0 ≤ pcap) (hscale : 0 ≤ Pscale)
    (hbad : 0 ≤ Pbad) (hpres : 0 ≤ Ppres) (hE : 0 ≤ E)
    (hPτ : 0 ≤ Pτ) (hPK : 0 ≤ PK) (hPF : 0 ≤ PF)
    (hτ : 0 < τ) (hτinv : τ⁻¹ ≤ Real.exp Pτ)
    (hforward : ∀ j, (forward j : ℝ) ≤ Real.exp PF)
    (hK : (K : ℝ) ≤ Real.exp PK) (hr : 1 ≤ r) :
    let Psm := forecastOriginalSmoothBudget m P
    let Pspatial := Pτ + 8
    let Pcoord := PK + PF + D
    let Pcut := PK + PF + 2 * D + normalizedSiteCutoffBound + 1
    let Lsp : ℝ≥0 := max ⟨8 / τ, by positivity⟩ 1
    let Lcoord := K * ∑ j, forward j * Fintype.card (J j)
    let Lcut := (Fintype.card (LayerSamplerAxis I n) * normalizedSiteCutoffBound / (2 * r)) * Lcoord
    let W := 4 * (Pscale + 8)
    let Pin := D * (allocatedInactivePointCapLog m D pcap 0 + W)
    let Pdec := (Pbad + Ppres) * ((Dmod + 2 : ℕ) : ℝ) * modularRankChargeFactor m
    let V := Pin + Pdec + (E + Psm) + 3
    let Esite := E + Psm + 1 + d * V
    let O := allocatedInactiveJointSiteLog m D (pcap + V) V (Esite + D * W) + W
    let Pperiod := V + D * O
    let Pfactor := Psm + D + O + 1 + Pspatial
    let Pnative := Pperiod + Pfactor + Pcoord + Pcut + 1
    let Pmass := Psm + d * V + D * O + 1
    let Pcap := Psm + Pin + Pdec + 1
    0 ≤ Pin ∧ 0 ≤ V ∧ 0 ≤ Esite ∧ 0 ≤ O ∧ 0 ≤ Pnative ∧
    ∃ (T : ℕ) (δ : ℝ), 0 < T ∧ (T : ℝ) ≤ Real.exp V ∧
      0 < δ ∧ δ ≤ 1 ∧ δ⁻¹ ≤ Real.exp Esite ∧
      ∀ S : LayerSamplerScale (G := G) B U basis R σ,
        let H := (allocatedOriginalForecastCap (X := X) B U basis S s hδslice : ℝ) + 1
        let L := allocatedOriginalForecastLip (X := X) B U basis S s hδslice
        H ≤ Real.exp Psm ∧ (L : ℝ) ≤ Real.exp Psm ∧
        (∀ (Rbad Qpres : ℕ) (Icap : ℝ), Icap ≤ Real.exp Pin →
          (Rbad : ℝ) ≤ Real.exp Pbad → (Qpres : ℝ) ≤ Real.exp Ppres →
          H * (Icap * ((((Rbad * Qpres : ℕ) : ℝ) ^
            (modularRankDecayExponent m (modularForecastRankConstant m Dmod : ℝ) *
              modularRankChargeFactor m)) / T) + (T : ℝ) ^ d * δ) ≤ Real.exp (-E)) ∧
        (∀ C : ℝ, 0 ≤ C → C ≤ Real.exp Pdec →
          H * Real.exp Pin * (1 + C) ≤ Real.exp Pcap) ∧
        (∀ a : ℕ, (a : ℝ) ≤ D →
          2 * H * ((T : ℝ) ^ d * Real.exp (a * O)) ≤ Real.exp Pmass) ∧
        (∀ (a q : ℕ), (a : ℝ) ≤ D → (q : ℝ) ≤ Real.exp (V + a * O) →
          (q : ℝ) ≤ Real.exp Pnative ∧
          (((L + a * ⟨Real.exp O, Real.exp_nonneg _⟩) * Lsp : ℝ≥0) : ℝ) ≤ Real.exp Pnative) ∧
        (Lcoord : ℝ) ≤ Real.exp Pnative ∧ (Lcut : ℝ) ≤ Real.exp Pnative := by
  intro Psm Pspatial Pcoord Pcut Lsp Lcoord Lcut W Pin Pdec V Esite O Pperiod Pfactor Pnative Pmass Pcap
  have hsm : 0 ≤ Psm := (forecastOriginalSmoothBudget_bounds m (zero_le_one.trans hP)).1
  have hspatial : 0 ≤ Pspatial := by dsimp only [Pspatial]; positivity
  have hcoord : 0 ≤ Pcoord := by dsimp only [Pcoord]; positivity
  have hcut : 0 ≤ Pcut := by dsimp only [Pcut]; positivity
  have hparameters := exists_forecast_early_approximation_budget m Dmod d
    hD hpcap hscale hsm hsm hbad hpres hE hspatial hcoord hcut
  obtain ⟨hPin, hV, hEsite, hO, hN, T, δ, hT, hTv, hδ, hδ1, hδb,
    herror, hcap, hmass, hfactor, hcoordN, hcutN⟩ := hparameters
  have hgeometry := forecast_ambient_coordinate_cutoff_exp_bounds
    (J := J) (Axis := LayerSamplerAxis I n) forward K r hD hPK hPF hdim haxes hforward hK hr
  have hspatialBound : (Lsp : ℝ) ≤ Real.exp Pspatial := by
    exact NNReal.coe_le_coe.mpr (forecast_spatial_coordinate_exp_bound hτ hPτ hτinv)
  refine ⟨hPin, hV, hEsite, hO, hN, T, δ, hT, hTv, hδ, hδ1, hδb, ?_⟩
  intro S H L
  have hactual := allocatedOriginalForecast_common_budget (X := X) B U basis S s hP hδslice
    hδsliceInv hX hZ (haxes.trans hDP) hblocks hprofile
  have hH : 0 ≤ H := by dsimp only [H]; positivity
  refine ⟨hactual.1, hactual.2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro Rbad Qpres Icap hI hRbad hQpres
    exact herror Rbad Qpres H Icap hH hactual.1 hI hRbad hQpres
  · intro C hC hCb
    exact hcap H C hH hactual.1 hC hCb
  · intro a ha
    exact hmass a H ha hH hactual.1
  · intro a q ha hq
    exact hfactor a q L Lsp ha hq hactual.2 hspatialBound
  · exact hgeometry.1.trans hcoordN
  · exact hgeometry.2.trans hcutN

end Erdos3.VectorPolynomial

end

end OAI
