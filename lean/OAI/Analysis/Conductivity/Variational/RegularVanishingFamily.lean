import Mathlib
import OAI.Analysis.Conductivity.Variational.ParametricGlobalCorrection
import OAI.Analysis.Conductivity.Sources.ParametricSymmetricSources

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Matrix Filter Topology
open scoped Matrix.Norms.Elementwise
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

theorem regular_vanishing_family_correction_of_moment
    {u : P×Coord3 → Fin 2 → ℝ} (hu : ContDiff ℝ (↑(⊤:ℕ∞)) u) (p : P) {U : Set Coord3}
    (hU : IsOpen U) (hUc : IsPreconnected U)
    (hD : ∀ x∈U,Function.Surjective (fderiv ℝ (fun y => u (p,y)) x))
    {K : Set Coord3} (hK : IsCompact K) (hKU : K⊆U)
    {r : Fin 2 → P×Coord3 → ℝ} {V : Set P} (hV : IsOpen V) (hp : p∈V)
    (hr : ∀ j,ContDiffOn ℝ (↑(⊤:ℕ∞)) (r j) (V×ˢuniv))
    (hs : ∀ᶠ q in 𝓝 p,PairSupported (fun j x => r j (q,x)) K)
    (hz : ∀ j x,r j (p,x)=0)
    {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ q in 𝓝 p,physicalSourceMoment (fun x => u (q,x)) (fun j x => r j (q,x))=0 →
      BoundedPhysicallyCorrectable (fun x => u (q,x)) U (fun j x => r j (q,x)) ε := by
  obtain ⟨L,hL,hsolve⟩ := parametric_global_regular_symmetric_correction_C0 hu p hU hUc hD hK hKU
  have hsmall (j) := compact_supported_family_C1_small hV hp (hr j) hK
    (hs.mono (fun q hq => hq j)) (hz j) (div_pos hε hL)
  have hall := Filter.eventually_all.mpr hsmall
  filter_upwards [hsolve,hall,hs,hV.mem_nhds hp] with q solve small supp hq mom
  have hsm (j) : ContDiff ℝ (↑(⊤:ℕ∞)) (fun x => r j (q,x)) := by
    rw [contDiff_iff_contDiffAt]
    intro x
    exact ((hr j).contDiffAt ((hV.prod isOpen_univ).mem_nhds ⟨hq,mem_univ x⟩)).comp x
      (contDiffAt_const.prodMk contDiffAt_id)
  have hcomp (j) : HasCompactSupport (fun x => r j (q,x)) :=
    hK.of_isClosed_subset (isClosed_tsupport _) (supp j)
  have hh := solve (fun j x => r j (q,x)) (fun j => ⟨hsm j,hcomp j⟩) supp mom
    (ε/L) (div_pos hε hL).le small
  simpa only [mul_div_cancel₀ ε hL.ne'] using hh

end ScalarConductivity

end
end

end OAI
