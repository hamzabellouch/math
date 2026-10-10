import Mathlib
import OAI.Analysis.Conductivity.Sources.ParametricPullback
import OAI.Analysis.Conductivity.Variational.LocalBoundedPiolaCorrection

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

def VanishingCorrectionRegion.piola
    {u v : P×Coord3 → Fin 2 → ℝ}
    (hu : ContDiff ℝ (↑(⊤:ℕ∞)) u) (hv : ContDiff ℝ (↑(⊤:ℕ∞)) v) (p : P)
    (Y : OpenPartialHomeomorph (P×Coord3) (P×Coord3))
    (hY : ∀ q x,(Y (q,x)).1=q)
    (hsm : ContDiff ℝ (↑(⊤:ℕ∞)) Y)
    (hinv : ContDiffOn ℝ (↑(⊤:ℕ∞)) Y.symm Y.target)
    {V : Set P} (hV : IsOpen V) (hp : p∈V) (hVb : Bornology.IsBounded V)
    {A U W K : Set Coord3} (hA : IsOpen A) (B : VanishingCorrectionRegion v p A)
    (hK : IsCompact K) (hKB : K⊆B.region) (hVA : V×ˢA⊆Y.target)
    (hW : ∀ q∈V,W⊆(fiberSlice Y hY q).symm '' K)
    (hWo : IsOpen W) (hWn : W.Nonempty) (hWb : Bornology.IsBounded W) (hWU : W⊆U)
    (himage : ∀ q∈V,(fiberSlice Y hY q).symm '' A⊆U)
    (hpot : ∀ q∈V,∀ y∈A,u (q,(fiberSlice Y hY q).symm y)=v (q,y))
    {C : ℝ} (hC : 0<C)
    (hbound : ∀ q∈V,∀ y∈A,
      let X := (fiberSlice Y hY q).symm
      9*|(fderiv ℝ X y).det|⁻¹*‖operatorMatrix (fderiv ℝ X y)‖*
        ‖operatorMatrix (fderiv ℝ X y)‖≤C) :
    VanishingCorrectionRegion u p U := by
  refine ⟨W,hWo,hWn,hWU,hWb,?_⟩
  intro r hr ε hε
  obtain ⟨R,hR,hRe⟩ := exists_parametric_source_pullback Y hY hsm hinv p hV hp hVb
    B.region_open B.region_bounded hK hKB (fun z hz => hVA ⟨hz.1,B.region_subset hz.2⟩) hW hr
  have hsolve := B.solve R hR (ε/C) (div_pos hε hC)
  filter_upwards [hRe,hsolve,hV.mem_nhds hp] with q he solve hq hm
  let X := (fiberSlice Y hY q).symm
  have hX : ContDiffOn ℝ (↑(⊤:ℕ∞)) X X.source := (fiberSlice_smooth Y hY hsm hinv q).2
  have hXi : ContDiffOn ℝ (↑(⊤:ℕ∞)) X.symm X.target :=
    (fiberSlice_smooth Y hY hsm hinv q).1.contDiffOn
  have hAs : A⊆X.source := fun y hy => hVA ⟨hq,hy⟩
  have huq : ContDiff ℝ (↑(⊤:ℕ∞)) (fun y => u (q,y)) := hu.comp (contDiff_const.prodMk contDiff_id)
  have hvq : ContDiff ℝ (↑(⊤:ℕ∞)) (fun y => v (q,y)) := hv.comp (contDiff_const.prodMk contDiff_id)
  have hps : EqOn (fun y => u (q,y)) ((fun y => v (q,y))∘X.symm) (X '' A) := by
    rintro _ ⟨y,hy,rfl⟩
    change u (q,X y)=v (q,X.symm (X y))
    rw [X.left_inv (hAs hy)]
    exact hpot q hq y hy
  have hrX (j) : tsupport (fun y => r j (q,y))⊆X.target :=
    (hr.supported q j).trans ((hW q hq).trans (by
      rintro _ ⟨y,hy,rfl⟩
      exact X.map_source (hAs (B.region_subset (hKB hy)))))
  have hre : (fun j => localPiolaSource X (fun y => R j (q,y)))=(fun j y => r j (q,y)) := by
    funext j
    rw [congrFun he j]
    exact localPiolaSource_inverse X (hX.differentiableOn (by simp))
      (hXi.differentiableOn (by simp)) _ ((subset_tsupport _).trans (hrX j))
  have hRs : PairSupported (fun j y => R j (q,y)) A := (hR.supported q).mono B.region_subset
  have hRm : physicalSourceMoment (fun y => v (q,y)) (fun j y => R j (q,y))=0 := by
    have hh := physicalSourceMoment_piola_local X hX hXi huq hvq hAs hps (hR.compact q) hRs
    rw [hre,hm] at hh
    exact hh.symm
  have hh := (solve hRm).piola_local X hX hXi huq hvq hA hAs hps hC.le
    (hbound q hq) (hR.compact q) hRs
  rw [hre,mul_div_cancel₀ ε hC.ne'] at hh
  exact hh.region_mono (himage q hq)

end ScalarConductivity

end
end

end OAI
