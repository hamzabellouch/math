import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanTiledSourceCell
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanTiledLinkedEndpoints
import OAI.GroupTheory.PolycyclicRecognition.Geometry.ExponentialQuotientSection
import OAI.GroupTheory.PolycyclicRecognition.Analysis.SectionProbeReparametrization
import OAI.GroupTheory.PolycyclicRecognition.Analysis.KernelHaarTransport

namespace OAI

/-! # Exact linked endpoints on the original source probability cell -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Set Metric
open scoped Manifold Pointwise

variable {EG G W I : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G,
    LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)
  (C : Set (H →ₗ[ℝ] ℝ))
  [Group I] [TopologicalSpace I] [IsTopologicalGroup I]
  [MeasurableSpace I] [BorelSpace I] [SecondCountableTopology I]


variable
    (ExpI : M.coneWordIdeal C → I)
    (bN : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (E : Fin 3 → Set W) (β : Fin 3 → M.ConeIdealBases C)
    (ambient : M.Bases) (t : Fin M.letterCount → ℝ) (scale : ℕ → ℝ)
    (φ : ℕ → I ≃ₜ* I) (ι : I →* F.N.carrier)
    (tiles : ℕ → ℕ) (anchor : ∀ n, Fin (tiles n) → I)
    (D : M.TiledProbeChainData T F hunimod eW C ExpI bN E β ambient t scale φ ι tiles anchor)
    (Q : NilpotentLieModel ((cartanRootIdeal H) ⧸ M.coneWordIdeal C))
    (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
    (chartQ : GroupLieAlgebra (𝓘(ℝ, Q.modelSpace)) Q.carrier ≃ₜ Q.carrier)
    (πQ : F.N.carrier →* Q.carrier)
    (hι : Topology.IsClosedEmbedding ι) (hrange : range ι = (πQ.ker : Set F.N.carrier))


local notation "Y" => fun n => TiledProbeChainData.sourceCell (T := T) (M := M) (F := F) (hunimod := hunimod) (eW := eW) (C := C)
    (ExpI := ExpI) (bN := bN) (E := E) (β := β) (ambient := ambient) (t := t)
    (scale := scale) (φ := φ) (ι := ι) (tiles := tiles) (anchor := anchor) (D := D) (Q := Q) (chartQ := chartQ) (πQ := πQ) (hι := hι) (hrange := hrange) n
local notation "ψ" => fun n => TiledProbeChainData.sourceCoordinates (T := T) (M := M) (F := F) (hunimod := hunimod) (eW := eW) (C := C)
    (ExpI := ExpI) (bN := bN) (E := E) (β := β) (ambient := ambient) (t := t)
    (scale := scale) (φ := φ) (ι := ι) (tiles := tiles) (anchor := anchor) (D := D) (Q := Q) (chartQ := chartQ) (πQ := πQ) (hι := hι) (hrange := hrange) n
local notation "σ" => TiledProbeChainData.sourceSection (T := T) (M := M) (F := F) (hunimod := hunimod) (eW := eW) (C := C)
    (ExpI := ExpI) (bN := bN) (E := E) (β := β) (ambient := ambient) (t := t)
    (scale := scale) (φ := φ) (ι := ι) (tiles := tiles) (anchor := anchor) (D := D) (Q := Q) (chartQ := chartQ) (chartN := chartN)

omit [IsTopologicalGroup I] [BorelSpace I] [SecondCountableTopology I] in
/-- The selected prefixes agree with the first probe, tile anchor and
second probe in the original source-cell coordinates. -/
theorem TiledProbeChainData.source_linked_endpoints
    (hchartN : ∀ v, chartN v = F.ExpN v)
    (k u : ℕ → F.N.carrier) (hφ : ∀ n z, ι (φ n z) = k n * ι z * (k n)⁻¹)
    (S : ℕ → MulAut F.N.carrier)
    (E' : Fin 3 → Set W) (γ : M.Bases) (t' : Fin M.letterCount → ℝ)
    (P : ∀ j, M.BoxProbeChains T F hunimod eW bN (E' j) γ t' scale
      (fun n (y : Y n) => S n (D.probe n j (ψ n y))))
    (origin base : ℕ → cartanRootIdeal H) (ε : ℕ → ℝ)
    (L : M.LinkedProbeChains T F hunimod eW bN E' γ t' scale
      (fun j n (y : Y n) => S n (D.probe n j (ψ n y))) P
      (fun n _ => origin n) (fun n _ => base n) ε)
    (horigin : ∀ n, F.ExpN (F.N.equiv (origin n)) = u n)
    (hbase : ∀ n, F.ExpN (F.N.equiv (base n)) = u n * S n (k n))
    (n : ℕ) (y : Y n) :
    F.ExpN (F.N.equiv (L.vertex 0 n y (Fin.last (P 0).length))) =
      u n * S n ((y.val.2 : F.N.carrier) * σ y.val.1) ∧
    F.ExpN (F.N.equiv (L.vertex 1 n y (Fin.last (P 1).length))) =
      coneProbeSecond (S n) (u n) (ι (anchor n (D.index n (ψ n y).2))) (k n) ∧
    F.ExpN (F.N.equiv (L.vertex 2 n y (Fin.last (P 2).length))) =
      coneProbeSecond (S n) (u n) (y.val.2 : F.N.carrier) (k n) := by
  let z := ψ n y
  have hback (i : I) : ι ((φ n).symm i) = (k n)⁻¹ * ι i * k n :=
    (intrinsic_probe_inverse_flow ι (φ n).toMulEquiv (k n) (hφ n) i).symm
  have e₁ : (u n * S n (k n)) * S n (D.probe n 1 z) =
      coneProbeSecond (S n) (u n) (ι (anchor n (D.index n z.2))) (k n) := by
    rw [D.second, hback]
    simp only [coneProbeSecond, map_mul, map_inv, mul_assoc, mul_inv_cancel_left]
  have e₂ : ((u n * S n (k n)) * S n (D.probe n 1 z)) * S n (D.probe n 2 z) =
      coneProbeSecond (S n) (u n) (ι z.2.val) (k n) := by
    rw [D.second, D.third, hback, hback]
    simp [coneProbeSecond, map_mul, mul_assoc]
  have hfirst := TiledProbeChainData.source_first (T := T) (M := M) (F := F) (hunimod := hunimod) (eW := eW) (C := C)
    (ExpI := ExpI) (bN := bN) (E := E) (β := β) (ambient := ambient) (t := t)
    (scale := scale) (φ := φ) (ι := ι) (tiles := tiles) (anchor := anchor) (D := D) (Q := Q) (chartQ := chartQ) (chartN := chartN)
    (πQ := πQ) (hι := hι) (hrange := hrange) hchartN n y
  have e₀ := L.first_exp n y (Fin.last (P 0).length)
  have e₁' := L.second_exp n y (Fin.last (P 1).length)
  have e₂' := L.third_exp n y (Fin.last (P 2).length)
  have e₀' := e₀.trans (congrArg₂ (fun a b : F.N.carrier => a * b)
    (horigin n) ((P 0).vertex_last n y))
  have h₁ := e₁'.trans (congrArg₂ (fun a b : F.N.carrier => a * b)
    (hbase n) ((P 1).vertex_last n y))
  have h₂ := e₂'.trans (congrArg₂ (fun a b : F.N.carrier => a * b)
    h₁ ((P 2).vertex_last n y))
  have hfirst' := e₀'.trans (congrArg (fun z => u n * S n z) hfirst)
  have hanchor := h₁.trans e₁
  have hsecond := h₂.trans e₂
  let eQ := TiledProbeChainData.sourceQuotientCoordinates (T := T) (M := M) (F := F) (hunimod := hunimod) (eW := eW) (C := C)
    (ExpI := ExpI) (bN := bN) (E := E) (β := β) (ambient := ambient) (t := t)
    (scale := scale) (φ := φ) (ι := ι) (tiles := tiles) (anchor := anchor) (D := D) (Q := Q) (chartQ := chartQ)
  have hi := sectionProbeCoordinates_snd eQ (kernelRealization πQ ι hι hrange).toHomeomorph
    (closedBall (0 : Fin (finrank ℝ
      (cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule)) → ℝ) 1)
    (M.coneIdealBox C ExpI ((M.supportIn T hunimod eW).weightSupport (E 0))
      (β 0) (scale n) 1) y
  have hi' : ι (ψ n y).2.val = (y.val.2 : F.N.carrier) := congrArg Subtype.val hi
  exact ⟨hfirst', hanchor, hsecond.trans (congrArg (fun i => coneProbeSecond (S n) (u n) i (k n)) hi')⟩

end PolycyclicRecognition.CartanWordModel

end

end OAI
