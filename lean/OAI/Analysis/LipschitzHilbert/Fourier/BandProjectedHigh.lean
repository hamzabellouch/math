import OAI.Analysis.LipschitzHilbert.Fourier.VerticalBinCost
import OAI.Analysis.LipschitzHilbert.Fourier.BandMeasurableHigh

namespace OAI

/-! The improved high-diagonal estimate for the actual vertically projected
input vectors. All projection size and energy hypotheses are discharged. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal BigOperators
namespace LipschitzHilbert.PacketRepresentation

theorem band_projected_high (hVariation : LepingleInput) (hLL : LaceyLiInput)
    (psi : SchwartzMap ℝ ℂ) (c C a M : ℝ)
    (hc : 0<c) (hC : 0<C) (ha : 0<a) (hM : 0<M)
    (hpsi : ∀ s : ℝ, psi s≠0 → a≤|s| ∧ |s|≤M) :
    ∃ D A L0 : ℝ, 0<D ∧ 0<A ∧ 16≤L0 ∧ ∀ L : ℝ, L0≤L →
    ∀ (N : ℕ) (topLength W w : ℝ), 0<topLength → 0<W → 0<w → w≤W →
      5*(w/W)≤c/2 → c/2≤C →
      topLength≤Real.exp (-(L^(97/100:ℝ))) →
      (∀ j : Fin N, D*w≤topLength/(2:ℝ)^j.val) →
    ∀ (field : Plane → ℝ), LipschitzWith 1 field → (∀ z, |field z|≤1/4) →
    ∀ (f g : ℝ×ℝ → ℂ), Measurable f → Measurable g →
      MemLp f 2 planeMeasure → MemLp g 2 planeMeasure →
      Integrable f planeMeasure → Integrable g planeMeasure →
    ∀ (F E ratio : ℝ), 0<F → 0<E → 0<ratio → E=ratio^2*F → Real.log ratio=L →
      (∀ z, ‖f z‖≤1) → (∀ z, ‖g z‖≤1) →
      (∫ z, ‖f z‖ ∂planeMeasure)≤F → (∫ z, ‖g z‖ ∂planeMeasure)≤E →
      (∫ z, ‖f z‖^2 ∂planeMeasure)≤F → (∫ z, ‖g z‖^2 ∂planeMeasure)≤E →
    ∀ l r m : ℝ, 600*(r-l)≤1 →
      (∀ z, z.1∉Icc l r → f z=0) → (∀ z, z.1∉Icc l r → g z=0) →
      Real.exp (L^(9/10:ℝ))≤m → m≤2*Real.exp (L^(9/10:ℝ)) → W=m*w →
      let I := verticalBinLabels ⌈C*W/w⌉₊ w W c C
      ‖finiteDiagonalBandL1 (N:=N) psi verticalBinPlateau topLength W
        (fun n : I => verticalBinCenter ⌈C*W/w⌉₊ W n)
        (fun z => field (planeCoordinates z))
        (fun n z => verticalConvolution
          (verticalProfileKernel verticalBinProfile W (verticalBinCenter ⌈C*W/w⌉₊ W n)) f z)
        (verticalBinVector I ⌈C*W/w⌉₊ W g)‖≤
        A*L^(-19:ℝ)*Real.sqrt F*Real.sqrt E := by
  let Qbase := (4*C+3)*(verticalBinKernelCost+1)
  have hQbase : 0<Qbase := mul_pos (by linarith) (by linarith [verticalBinKernelCost_nonneg])
  obtain ⟨D,A,L0,hD,hA,hL0,hmain⟩ := band_diagonal_measurable_high hVariation hLL
    psi verticalBinPlateau 4 (c/2) (2*C) a M (by norm_num) (by positivity) (by positivity) ha hM
    hpsi (fun y hy => by simpa only [show (4:ℝ)/2=2 by norm_num] using verticalBinPlateau_support y hy)
    1 Qbase 1 (by norm_num) hQbase (by norm_num)
  refine ⟨D,A,L0,hD,hA,hL0,?_⟩
  intro L hL N topLength W w htop hW hw hwW hsmall hcC htime hlength
    field hfield hfieldBound f g hfm hgm hf2 hg2 hf1 hg1 F E ratio hF hE hr heq hlog
    hfInf hgInf hfL1 hgL1 hfE hgE l r m hstrip hfstrip hgstrip hmlo hmhi hWeq
  let I := verticalBinLabels ⌈C*W/w⌉₊ w W c C
  let fv := verticalBinVector I ⌈C*W/w⌉₊ W f
  let gv := verticalBinVector I ⌈C*W/w⌉₊ W g
  have hI : I⊆Finset.range (2*⌈C*W/w⌉₊+1) := Finset.filter_subset _ _
  have hfe := verticalBinVector_energy I ⌈C*W/w⌉₊ W hW hI f hfm hf2
  have hge := verticalBinVector_energy I ⌈C*W/w⌉₊ W hW hI g hgm hg2
  have hfl := verticalBinVector_l1 I ⌈C*W/w⌉₊ W hW f hfm hf1
  have hgl := verticalBinVector_l1 I ⌈C*W/w⌉₊ W hW g hgm hg1
  have hQ := verticalBinVectorCost_nonneg w W c C
  have hQgrowth : verticalBinVectorCost w W c C≤Qbase*Real.exp (1*L^(9/10:ℝ)) := by
    simpa only [one_mul,Qbase] using verticalBinVectorCost_growth w W c C L m hw hW hC
      (by linarith) hWeq hmhi
  have hfbound (z) : ‖fv z‖≤verticalBinVectorCost w W c C := by
    simpa only [fv,I,verticalBinVectorCost,mul_one] using
      verticalBinVector_uniform I ⌈C*W/w⌉₊ W hW f 1 hfInf z
  have hgbound (z) : ‖gv z‖≤verticalBinVectorCost w W c C := by
    simpa only [gv,I,verticalBinVectorCost,mul_one] using
      verticalBinVector_uniform I ⌈C*W/w⌉₊ W hW g 1 hgInf z
  have hf1v : (∫ z, ‖fv z‖ ∂planeMeasure)≤verticalBinVectorCost w W c C*F :=
    hfl.2.trans (mul_le_mul_of_nonneg_left hfL1 hQ)
  have hg1v : (∫ z, ‖gv z‖ ∂planeMeasure)≤verticalBinVectorCost w W c C*E :=
    hgl.2.trans (mul_le_mul_of_nonneg_left hgL1 hQ)
  have hfvstrip : ∀ z, fv z≠0 → z.1∈Icc l r := by
    intro z hz
    by_contra h
    exact hz (verticalBinVector_horizontal_support I ⌈C*W/w⌉₊ W f (Icc l r) hfstrip z h)
  have hgvstrip : ∀ z, gv z≠0 → z.1∈Icc l r := by
    intro z hz
    by_contra h
    exact hz (verticalBinVector_horizontal_support I ⌈C*W/w⌉₊ W g (Icc l r) hgstrip z h)
  exact hmain L hL N I topLength W w htop hW hw hwW htime hlength
    (fun n => verticalBinCenter ⌈C*W/w⌉₊ W n)
    (fun n => (verticalBinLabels_admissible_centers _ w W c C hsmall hcC n).1)
    (fun n => (verticalBinLabels_admissible_centers _ w W c C hsmall hcC n).2)
    field hfield hfieldBound fv gv (verticalBinVector_measurable I _ W f hfm)
    (verticalBinVector_measurable I _ W g hgm) hfe.1 hge.1 hfl.1.norm hgl.1.norm
    F E ratio (verticalBinVectorCost w W c C) hF hE hr heq hlog hQ hQgrowth hfbound hgbound
    hf1v hg1v (by simpa only [one_mul] using hfe.2.trans hfE)
    (by simpa only [one_mul] using hge.2.trans hgE)
    l r m hstrip hfvstrip hgvstrip hmlo hmhi hWeq

end LipschitzHilbert.PacketRepresentation

end

end OAI
