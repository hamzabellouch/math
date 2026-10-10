import OAI.GroupTheory.PolycyclicRecognition.Geometry.RescaledHeightLegs
import OAI.GroupTheory.PolycyclicRecognition.Analysis.AffineProfileControlledPaths
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanDirectionalVisits
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanGradedGeometry

namespace OAI

/-! # Actual controlled paths from the selected affine profiles -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Set Filter
open scoped Manifold Topology NNReal

variable {EG G W I : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G] [IsIsometricSMul G G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [Fintype I] [DecidableEq I]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H) [Nonempty (Fin M.letterCount)]
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

/-- One compact set of Cartan coordinates suffices for all the selected
finite chains. Good affine profiles on that set produce actual paths with
linear length, logarithmic jumps, and the prescribed convex height image. -/
theorem exists_selected_profile_paths
    (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
    (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)
    (π : G →* Multiplicative W)
    (hπ : ∀ x, (π (Exp x)).toAdd = eW (heightProjection T.character x))
    (X : I → H) {d : ℕ} (hDnil : lowerCentralSeries ℝ H H d = ⊥)
    (bD₀ : Basis (Fin (finrank ℝ H)) ℝ H)
    (βD : WordBasisSelections X (boundedBracketWords d))
    (hβD : IsMaximizingColumnBasis (wordListCoordinates X (boundedBracketWords d) bD₀)
      (fun w => bracketWordExponent (fun _ : I => 1) w) βD.val)
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop) (hscale0 : ∀ n, 0 < scale n)
    (pivot : H) (v : Fin M.letterCount → H)
    (E V : Set W) (hE : Convex ℝ E) (hpivot : eW (heightProjection T.character pivot) ∈ E)
    (hV : IsOpen V) (hVconv : Convex ℝ V) (hEV : E ⊆ V)
    (hv : ∀ i, eW (heightProjection T.character (pivot + v i : H)) ∈ E)
    (s : Fin M.letterCount → ℝ)
    (hs : ∀ i, cartanHeightWeight T H (M.weight i)
      (eW.symm (eW (heightProjection T.character (pivot + v i : H)))) = s i)
    {B : ℝ} (hB : 0 ≤ B) :
    let b := WordBasisSelections.basis X (boundedBracketWords d) βD
    let cost := fun j => bracketWordExponent (fun _ : I => 1) (βD.val j)
    let br := fun n => exponentialRescaleBasis b cost (Real.log (scale n))
    let h : H →ₗ[ℝ] W := eW.toLinearMap.comp
      ((heightProjection T.character).comp H.incl.toLinearMap)
    ∃ (Q : Set (Fin (finrank ℝ H) → ℝ)) (C : ℝ),
      IsCompact Q ∧ Q ⊆ {z | h (b.equivFun.symm z) ∈ V} ∧ 0 ≤ C ∧
      (∀ᶠ n in atTop, (br n).equivFun (scale n • pivot) ∈ Q) ∧
      ∀ᶠ n in atTop, ∀ (N : ℕ) (x : G) (vertex : Fin (N + 1) → G)
        (mode : Fin N → Fin M.letterCount) (coeff : Fin N → ℝ),
        (∀ j, vertex j.succ = vertex j.castSucc *
          Exp (coeff j • (M.letter (mode j) : GroupLieAlgebra (𝓘(ℝ, EG)) G))) →
        (∀ j, |coeff j| ≤ B * Real.exp (scale n * s (mode j))) →
        ∀ (J : G → W) (K : ℝ≥0), LipschitzWith K J →
        ∀ (A : W →ₗ[ℝ] W) (offset : W) (ε : ℝ),
        (∀ i z, z ∈ Q → h (b.equivFun.symm z) ∈ E →
          ‖rescaledMapProfile J x (vertex i) (Real.log (scale n))
              (fun z => Exp ((br n).equivFun.symm z)) z -
            (A (h (b.equivFun.symm z)) + offset)‖ ≤ ε) →
        ∃ path : Path (x * vertex 0 * Exp (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G)))
          (x * vertex (Fin.last N) * Exp (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G))),
          PathMetricBound path ((C * scale n) * 2 ^ N)
            ((C * (1 + Real.log (2 + scale n))) * 2 ^ N) ∧
          ∀ t, ∃ w ∈ E,
            ‖J (path t) - J (x * vertex 0 * Exp (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G))) -
              scale n • A (w - h pivot)‖ ≤
                2 * scale n * ε + K * (C * Real.log (2 + scale n)) := by
  classical
  let _ : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, EG)) ⊤
  dsimp only
  let b := WordBasisSelections.basis X (boundedBracketWords d) βD
  let cost := fun j => bracketWordExponent (fun _ : I => 1) (βD.val j)
  let br := fun n => exponentialRescaleBasis b cost (Real.log (scale n))
  let h : H →ₗ[ℝ] W := eW.toLinearMap.comp
    ((heightProjection T.character).comp H.incl.toLinearMap)
  let EH : H → G := fun u => Exp u
  have hh (u w : H) : h ⁅u, w⁆ = 0 := by
    change eW (heightProjection T.character ⁅(u : GroupLieAlgebra (𝓘(ℝ, EG)) G), w⁆) = 0
    rw [T.height_lie, map_zero]
  obtain ⟨⟨chartD, hchartD⟩, _⟩ := haarD.2 F.ExpD F.isExpD
    (F.D.tangent_nilpotent inferInstance)
  have hinj : Function.Injective EH := by
    have hi := F.closedD.injective.comp
      ((funext hchartD ▸ chartD.bijective).injective.comp F.D.equiv.injective)
    intro u w he
    apply hi
    change F.inclusionD (F.ExpD (F.D.equiv u)) = F.inclusionD (F.ExpD (F.D.equiv w))
    rw [F.compatibleD, F.compatibleD]
    exact he
  obtain ⟨aD, _, hmD⟩ := model_finiteDynkinExpansion dynkinD F.D.equiv F.ExpD F.isExpD hDnil 2
  have hm (u w : H) : EH (finiteDynkinPolynomial aD ![u, w]) = EH u * EH w := by
    have hm' := congrArg F.inclusionD (hmD ![u, w]).symm
    simpa [EH, F.compatibleD, List.ofFn_succ] using hm'
  have hweight := maximizing_word_basis_bracket_weight X hDnil bD₀ (fun _ => 1) βD hβD
  obtain ⟨Q, hQ, hQV, hlegs⟩ := exists_compact_rescaled_height_legs
    X (boundedBracketWords d) βD h hh EH hinj (by simp [EH, hExp.map_zero])
    π (fun u => hπ u) aD hm hweight scale hscale hscale0 pivot
    (fun i => pivot + v i) V hV hVconv (hEV hpivot) (fun i => hEV (hv i))
  have hs' i : cartanHeightWeight T H (M.weight i)
      (eW.symm (h pivot + eW (heightProjection T.character (v i)))) = s i := by
    have hsi := hs i
    change cartanHeightWeight T H (M.weight i) (eW.symm (h (pivot + v i))) = s i at hsi
    rw [map_add] at hsi
    exact hsi
  obtain ⟨C, hC, hvisit⟩ := M.exists_directional_visit_bound T F hExp realize haarD dynkinD
    eW π hπ v (h pivot) s hs' (norm_nonneg ((finBasis ℝ H).equivFun pivot)) hB 1
  refine ⟨Q, C, hQ, hQV, hC, hlegs.mono (fun _ hn => hn.1), ?_⟩
  filter_upwards [hlegs] with n hn
  intro N x vertex mode coeff hstep hamp J K hJ A offset ε hgood
  let r := scale n
  have hr : 0 ≤ r := (hscale0 n).le
  let z₀ := (br n).equivFun (r • pivot)
  have hz₀ : z₀ ∈ Q := hn.1
  have hφ₀ : Exp ((br n).equivFun.symm z₀) = Exp (r • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G)) := by
    simp only [z₀, LinearEquiv.symm_apply_apply, SetLike.val_smul]
  have hq₀ : h (b.equivFun.symm z₀) = h pivot := by
    have hc : h ((br n).equivFun.symm z₀) = r • h (b.equivFun.symm z₀) := by
      simpa only [br, cost, bracketWordExponent_one] using
        word_length_chart_height X (boundedBracketWords d) βD h hh (hscale0 n) z₀
    rw [show (br n).equivFun.symm z₀ = r • pivot from (br n).equivFun.symm_apply_apply _,
      map_smul] at hc
    exact ((smul_right_injective W (hscale0 n).ne') hc).symm
  have hex (j : Fin N) (t : unitInterval) : ∃ z ∈ Q,
      Exp ((br n).equivFun.symm z) =
        Exp (r • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G)) *
          Exp ((r * (t : ℝ)) • (v (mode j) : GroupLieAlgebra (𝓘(ℝ, EG)) G)) ∧
      h (b.equivFun.symm z) = h pivot + (t : ℝ) • h (v (mode j)) := by
    obtain ⟨z, hz, he, hheight⟩ := hn.2 (mode j) t t.property
    refine ⟨z, hz, ?_, ?_⟩
    · simpa only [EH, add_sub_cancel_left, SetLike.val_smul] using he
    · simpa only [map_add, add_sub_cancel_left] using hheight
  choose leg hleg hlegφ hlegq using hex
  let dd (j : Fin N) (t : ℝ) := Exp (t • (v (mode j) : GroupLieAlgebra (𝓘(ℝ, EG)) G))
  let ff (j : Fin N) (t : ℝ) := Exp (t • (M.letter (mode j) : GroupLieAlgebra (𝓘(ℝ, EG)) G))
  have hd j : Continuous (dd j) := continuous_exp_line_of_published_realization T Exp hExp realize _
  have hf j : Continuous (ff j) := continuous_exp_line_of_published_realization T Exp hExp realize _
  have hd₀ j : dd j 0 = 1 := by simp [dd, hExp.map_zero]
  have hf₀ j : ff j 0 = 1 := by simp [ff, hExp.map_zero]
  have hpbound : ‖(finBasis ℝ H).equivFun (r • pivot)‖ ≤
      ‖(finBasis ℝ H).equivFun pivot‖ * (1 + r) ^ 1 := by
    rw [map_smul, norm_smul, Real.norm_of_nonneg hr, pow_one]
    nlinarith [norm_nonneg ((finBasis ℝ H).equivFun pivot)]
  have hpheight : (π (Exp (r • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G)))).toAdd = r • h pivot := by
    rw [hπ, map_smul, map_smul]
    rfl
  have hb := hvisit r hr (r • pivot) hpbound hpheight
  have hlog : 0 ≤ Real.log (2 + r) := Real.log_nonneg (by linarith)
  have hElegs (j : Fin N) (t : unitInterval) :
      h (b.equivFun.symm (leg j t)) - h (b.equivFun.symm z₀) ∈
        (fun w => w - h pivot) '' E := by
    rw [hlegq, hq₀]
    refine ⟨h pivot + (t : ℝ) • h (v (mode j)), ?_, rfl⟩
    have ht := hE hpivot (hv (mode j)) (sub_nonneg.mpr t.property.2)
      t.property.1 (show (1 - (t : ℝ)) + t = 1 by ring)
    change (1 - (t : ℝ)) • h pivot + (t : ℝ) • h (pivot + v (mode j)) ∈ E at ht
    have heq : (1 - (t : ℝ)) • h pivot + (t : ℝ) • h (pivot + v (mode j)) =
        h pivot + (t : ℝ) • h (v (mode j)) := by rw [map_add]; module
    rwa [heq] at ht
  have hmetric (j : Fin N) : PathMetricBound
      (supportVisitPath (dd j) (hd j) (hd₀ j) (ff j) (hf j) (hf₀ j)
        (x * vertex j.castSucc) (Exp ((br n).equivFun.symm z₀))
        (Real.exp (Real.log r)) (coeff j))
      (C * r) (C * (1 + Real.log (2 + r))) := by
    rw [hφ₀, Real.exp_log (show 0 < r from hscale0 n)]
    simpa only [dd, ff, directionalVisitPath, SetLike.val_smul] using
      (hb (x * vertex j.castSucc) (mode j) (coeff j) (hamp j)).1
  have hswitch (j : Fin N) (t : unitInterval) :
      dist ((x * vertex j.castSucc) * ff j ((t : ℝ) * coeff j) *
        (Exp ((br n).equivFun.symm z₀) * dd j (Real.exp (Real.log r))))
        (((x * vertex j.castSucc) * Exp ((br n).equivFun.symm z₀)) *
          dd j (Real.exp (Real.log r))) ≤ C * Real.log (2 + r) := by
    have hh := (hb (x * vertex j.castSucc) (mode j) (coeff j) (hamp j)).2
      t t.property 0 ⟨le_rfl, zero_le_one⟩
    rw [hφ₀, Real.exp_log (show 0 < r from hscale0 n)]
    simpa only [dd, ff, zero_mul, zero_smul, SetLike.val_smul,
      hExp.map_zero, mul_one, mul_assoc] using hh
  obtain ⟨path, hpath, himage⟩ := exists_affine_profile_controlled_path x vertex
    (fun z => Exp ((br n).equivFun.symm z)) (fun z => h (b.equivFun.symm z)) z₀
    dd ff hd hd₀ hf hf₀ coeff hstep J hJ A offset (Real.log r) ε
    (C * r) (C * (1 + Real.log (2 + r))) (C * Real.log (2 + r))
    (mul_nonneg hC hr) (mul_nonneg hC (by linarith)) (mul_nonneg hC hlog)
    (Q ∩ {z | h (b.equivFun.symm z) ∈ E}) ⟨hz₀, by
      change h (b.equivFun.symm z₀) ∈ E
      rwa [hq₀]⟩
    (fun i z hz => hgood i z hz.1 hz.2)
    ((fun w => w - h pivot) '' E) ⟨h pivot, hpivot, sub_self _⟩
    leg (fun j t => ⟨hleg j t, by
      obtain ⟨w, hw, he⟩ := hElegs j t
      rw [hq₀] at he
      change h (b.equivFun.symm (leg j t)) ∈ E
      exact (sub_left_inj.mp he) ▸ hw⟩) (fun j t => by rw [Real.exp_log (hscale0 n), hφ₀]; exact hlegφ j t)
    hElegs hmetric hswitch
  let path' := path.cast (by rw [hφ₀]) (by rw [hφ₀])
  refine ⟨path', hpath, ?_⟩
  intro t
  obtain ⟨_, ⟨w, hw, rfl⟩, hbound⟩ := himage t
  simp only [Real.exp_log (show 0 < r from hscale0 n), hφ₀] at hbound
  exact ⟨w, hw, hbound⟩

end PolycyclicRecognition.CartanWordModel

end

end OAI
