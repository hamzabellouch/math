import Mathlib
import OAI.Analysis.Conductivity.Walls.CriticalWallTensor
import OAI.Analysis.Conductivity.Variational.ParametricSpatialDerivative

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

lemma gradientColumns_parametric_smoothOn {u : P×Coord3 → Fin 2 → ℝ}
    {V : Set (P×Coord3)} (hV : IsOpen V) (hu : ContDiffOn ℝ (↑(⊤:ℕ∞)) u V) :
    ContDiffOn ℝ (↑(⊤:ℕ∞)) (fun q => gradientColumns (fderiv ℝ (fun x => u (q.1,x)) q.2)) V := by
  apply contDiffOn_pi.mpr
  intro i
  apply contDiffOn_pi.mpr
  intro j
  exact (contDiffOn_pi.mp ((spatialFDeriv_smoothOn hV hu).clm_apply contDiffOn_const)) j

lemma coordinateDivergence_parametric_smoothOn {f : P×Coord3 → Coord3}
    {V : Set (P×Coord3)} (hV : IsOpen V) (hf : ContDiffOn ℝ (↑(⊤:ℕ∞)) f V) :
    ContDiffOn ℝ (↑(⊤:ℕ∞)) (fun q => coordinateDivergence (fun x => f (q.1,x)) q.2) V := by
  apply ContDiffOn.sum
  intro i _
  exact (spatialFDeriv_smoothOn hV (contDiffOn_pi.mp hf i)).clm_apply contDiffOn_const

lemma symmetricSource_parametric_smoothOn {H : P×Coord3 → Mat3} {u : P×Coord3 → Fin 2 → ℝ}
    {V : Set (P×Coord3)} (hV : IsOpen V) (hH : ContDiffOn ℝ (↑(⊤:ℕ∞)) H V)
    (hu : ContDiffOn ℝ (↑(⊤:ℕ∞)) u V) (j : Fin 2) :
    ContDiffOn ℝ (↑(⊤:ℕ∞)) (fun q => symmetricSource (fun x => H (q.1,x)) (fun x => u (q.1,x)) j q.2) V := by
  apply coordinateDivergence_parametric_smoothOn hV
    (f:=fun q : P×Coord3 => (H q*gradientColumns (fderiv ℝ (fun x => u (q.1,x)) q.2)).col j)
  have hg := gradientColumns_parametric_smoothOn hV hu
  apply contDiffOn_pi.mpr
  intro i
  change ContDiffOn ℝ (↑(⊤:ℕ∞)) (fun q => ∑ k, H q i k *
    gradientColumns (fderiv ℝ (fun x => u (q.1,x)) q.2) k j) V
  apply ContDiffOn.sum
  intro k _
  exact (contDiffOn_pi.mp (contDiffOn_pi.mp hH i) k).mul
    (contDiffOn_pi.mp (contDiffOn_pi.mp hg k) j)

lemma wallCoordinatePair_parametric_smooth {v : P×Box3 → ℝ}
    (hv : ContDiff ℝ (↑(⊤:ℕ∞)) v) :
    ContDiff ℝ (↑(⊤:ℕ∞)) (fun q : P×Coord3 => wallCoordinatePair (fun y => v (q.1,y)) q.2) := by
  apply contDiff_pi.mpr
  intro j
  fin_cases j
  · exact (contDiff_apply ℝ ℝ (0:Fin 3)).comp contDiff_snd
  · exact hv.comp (contDiff_fst.prodMk (boxCoordinates.contDiff.comp contDiff_snd))

lemma wallMatrix_parametric_smoothOn {A B : P×Box3 → ℝ} {V : Set P}
    (hA : ContDiffOn ℝ (↑(⊤:ℕ∞)) A (V×ˢuniv))
    (hB : ContDiffOn ℝ (↑(⊤:ℕ∞)) B (V×ˢuniv)) :
    ContDiffOn ℝ (↑(⊤:ℕ∞)) (fun q : P×Coord3 =>
      wallMatrix (fun y => A (q.1,y)) (fun y => B (q.1,y)) q.2) (V×ˢuniv) := by
  have hm : ContDiff ℝ (↑(⊤:ℕ∞)) (fun q : P×Coord3 => (q.1,boxCoordinates q.2)) :=
    contDiff_fst.prodMk (boxCoordinates.contDiff.comp contDiff_snd)
  have hmap : MapsTo (fun q : P×Coord3 => (q.1,boxCoordinates q.2)) (V×ˢuniv) (V×ˢuniv) :=
    fun q hq => ⟨hq.1,mem_univ _⟩
  apply contDiffOn_pi.mpr
  intro i
  apply contDiffOn_pi.mpr
  intro j
  fin_cases i <;> fin_cases j
  all_goals first | exact contDiffOn_const | exact hA.comp hm.contDiffOn hmap |
    exact hB.comp hm.contDiffOn hmap

end ScalarConductivity

end


noncomputable section
namespace ScalarConductivity
open Set Filter Topology

variable {P E F : Type*} [TopologicalSpace P] [TopologicalSpace E]
  [NormedAddCommGroup F]

lemma compact_parametric_norm_small {f : P×E → F} {p : P} {K : Set E}
    (hK : IsCompact K) (hf : ∀ x∈K,ContinuousAt f (p,x))
    (hz : ∀ x∈K,f (p,x)=0) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ q in 𝓝 p,∀ x∈K,‖f (q,x)‖≤ε := by
  apply hK.eventually_forall_of_forall_eventually
  intro x hx
  have hn : ‖f (p,x)‖<ε := by rw [hz x hx,norm_zero]; exact hε
  exact ((hf x hx).norm.eventually_lt_const hn).mono (fun _ h => h.le)

end ScalarConductivity

namespace ScalarConductivity
open Set Filter Topology
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

lemma compact_supported_family_C1_small {f : P×Coord3 → ℝ} {p : P} {V : Set P}
    (hV : IsOpen V) (hp : p∈V) (hf : ContDiffOn ℝ (↑(⊤:ℕ∞)) f (V×ˢuniv))
    {K : Set Coord3} (hK : IsCompact K)
    (hs : ∀ᶠ q in 𝓝 p,tsupport (fun x => f (q,x))⊆K)
    (hz : ∀ x,f (p,x)=0) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ q in 𝓝 p,UniformC1Bound (fun x => f (q,x)) ε := by
  have hopen : IsOpen (V×ˢ(univ : Set Coord3)) := hV.prod isOpen_univ
  have hc (x : Coord3) : ContDiffAt ℝ (↑(⊤:ℕ∞)) f (p,x) :=
    hf.contDiffAt (hopen.mem_nhds ⟨hp,mem_univ x⟩)
  have hd := spatialFDeriv_smoothOn hopen hf
  have he : (fun x => f (p,x))=fun _ => 0 := funext hz
  have hzD (x : Coord3) : spatialFDeriv f (p,x)=0 := by
    dsimp [spatialFDeriv]; rw [he]; simp
  have hv := compact_parametric_norm_small hK (fun x _ => (hc x).continuousAt)
    (fun x _ => hz x) hε
  have hder := compact_parametric_norm_small hK
    (fun x _ => (hd.contDiffAt (hopen.mem_nhds ⟨hp,mem_univ x⟩)).continuousAt)
    (fun x _ => hzD x) hε
  filter_upwards [hs,hv,hder] with q hq hv hd
  intro x
  by_cases hx : x∈K
  · exact ⟨by simpa only [Real.norm_eq_abs] using hv x hx,hd x hx⟩
  · have hn : x∉tsupport (fun y => f (q,y)) := fun hh => hx (hq hh)
    have hv : f (q,x)=0 := image_eq_zero_of_notMem_tsupport (f:=fun y => f (q,y)) hn
    have hd := fderiv_of_notMem_tsupport ℝ hn
    exact ⟨by change |f (q,x)|≤ε; rw [hv,abs_zero]; exact hε.le,by rw [hd,norm_zero]; exact hε.le⟩

end ScalarConductivity

end

end OAI
