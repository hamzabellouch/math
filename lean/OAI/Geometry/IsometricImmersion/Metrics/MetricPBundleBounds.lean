import OAI.Geometry.IsometricImmersion.Metrics.UniversalMetricP
import OAI.Geometry.IsometricImmersion.Calculus.NormedCoordinateCalculus

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology BigOperators Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry

section FiniteProducts
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem norm_iteratedFDeriv_pi_le {ι : Type*} [Fintype ι]
    {f : E → ι → F} {p : E} (hf : ContDiffAt ℝ ∞ f p)
    (n : ℕ) {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ i, ‖iteratedFDeriv ℝ n (fun x => f x i) p‖ ≤ M) :
    ‖iteratedFDeriv ℝ n f p‖ ≤ M := by
  have heq : iteratedFDeriv ℝ n f p =
      ContinuousMultilinearMap.pi (fun i => iteratedFDeriv ℝ n (fun x => f x i) p) := by
    ext v i
    have hh := congrArg (fun L => L v)
      ((ContinuousLinearMap.proj i : (ι → F) →L[ℝ] F).iteratedFDeriv_comp_left
        hf (WithTop.coe_le_coe.mpr le_top) (i := n))
    exact hh.symm
  rw [heq, ContinuousMultilinearMap.opNorm_pi]
  exact (pi_norm_le_iff_of_nonneg hM).mpr hb

theorem norm_iteratedFDeriv_prod_le {f : E → F} {g : E → G} {p : E}
    (hf : ContDiffAt ℝ ∞ f p) (hg : ContDiffAt ℝ ∞ g p)
    (n : ℕ) {M : ℝ}
    (hfB : ‖iteratedFDeriv ℝ n f p‖ ≤ M)
    (hgB : ‖iteratedFDeriv ℝ n g p‖ ≤ M) :
    ‖iteratedFDeriv ℝ n (fun x => (f x, g x)) p‖ ≤ M := by
  rw [iteratedFDeriv_prodMk hf hg (WithTop.coe_le_coe.mpr le_top),
    ContinuousMultilinearMap.opNorm_prod]
  exact max_le hfB hgB

theorem norm_iteratedFDeriv_comp_contraction
    (L : E →L[ℝ] F) {f : F → G} {U : Set F}
    (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U) (hL : ‖L‖ ≤ 1)
    {p : E} (hp : L p ∈ U) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (f ∘ L) p‖ ≤ ‖iteratedFDeriv ℝ n f (L p)‖ := by
  have hpre : IsOpen (L ⁻¹' U) := hU.preimage L.continuous
  rw [← iteratedFDerivWithin_of_isOpen n hpre hp,
    L.iteratedFDerivWithin_comp_right hf hU.uniqueDiffOn hpre.uniqueDiffOn hp
      (WithTop.coe_le_coe.mpr le_top),
    iteratedFDerivWithin_of_isOpen n hU hp]
  exact ((iteratedFDeriv ℝ n f (L p)).norm_compContinuousLinearMap_le
    (fun _ => L)).trans (by
      calc
        _ ≤ ‖iteratedFDeriv ℝ n f (L p)‖ * ∏ _ : Fin n, (1 : ℝ) :=
          mul_le_mul_of_nonneg_left (Finset.prod_le_prod₀ (fun _ _ => norm_nonneg L)
            (fun _ _ => hL)) (norm_nonneg _)
        _ = _ := by simp)

theorem norm_iteratedFDeriv_id_pos (p : E) {n : ℕ} (hn : 1 ≤ n) :
    ‖iteratedFDeriv ℝ n (fun x : E => x) p‖ ≤ 1 := by
  cases n with
  | zero => omega
  | succ n =>
    rw [← norm_iteratedFDeriv_fderiv]
    have he : fderiv ℝ (fun x : E => x) = (fun _ : E => ContinuousLinearMap.id ℝ E) := by
      funext x
      exact fderiv_fun_id
    rw [he]
    cases n with
    | zero => simpa using (ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := E))
    | succ n => simp only [iteratedFDeriv_succ_const]; norm_num
end FiniteProducts

theorem norm_iteratedFDeriv_coordPartial_le {f : Coord → ℝ} {U : Set Coord}
    (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U) {p : Coord} (hp : p ∈ U)
    (i : Fin 2) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (coordPartial i f) p‖ ≤
      ‖iteratedFDeriv ℝ (n + 1) f p‖ := by
  have hd : ContDiffAt ℝ ∞ (fderiv ℝ f) p :=
    (hf.fderiv_of_isOpen hU (by simp)).contDiffAt (hU.mem_nhds hp)
  have hh := norm_iteratedFDeriv_clm_apply_const (c := Pi.single i (1 : ℝ))
    hd (n := n) (WithTop.coe_le_coe.mpr le_top)
  have he : (fun y : Coord => fderiv ℝ f y (Pi.single i (1 : ℝ))) = coordPartial i f := by
    funext y
    rfl
  rw [he, Pi.norm_single, norm_one, one_mul, norm_iteratedFDeriv_fderiv] at hh
  exact hh

def statePointCLM : DarbouxState →L[ℝ] Coord :=
  ContinuousLinearMap.pi (fun i =>
    if i = 0 then ContinuousLinearMap.proj 0 else ContinuousLinearMap.proj 1)

theorem statePointCLM_eq (w : DarbouxState) : statePointCLM w = statePoint w := by
  ext i
  fin_cases i <;> simp [statePointCLM, statePoint]

theorem statePointCLM_norm_le : ‖statePointCLM‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro w
  rw [one_mul, statePointCLM_eq]
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg w)).mpr
  intro i
  fin_cases i
  · exact norm_le_pi_norm w 0
  · exact norm_le_pi_norm w 1

theorem norm_iteratedFDeriv_comp_statePoint {f : Coord → ℝ} {U : Set Coord}
    (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U) {w : DarbouxState}
    (hw : statePoint w ∈ U) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun v => f (statePoint v)) w‖ ≤
      ‖iteratedFDeriv ℝ n f (statePoint w)‖ := by
  have hp : statePointCLM w ∈ U := by
    rw [statePointCLM_eq]
    exact hw
  have hnumerical : ‖iteratedFDeriv ℝ n (f ∘ statePointCLM) w‖ ≤
      ‖iteratedFDeriv ℝ n f (statePointCLM w)‖ :=
    norm_iteratedFDeriv_comp_contraction statePointCLM hf hU statePointCLM_norm_le hp n
  have he : (fun v => f (statePoint v)) = f ∘ statePointCLM := by
    funext v
    change f (statePoint v) = f (statePointCLM v)
    rw [statePointCLM_eq]
  rw [he, ← statePointCLM_eq w]
  exact hnumerical

theorem metricPBundle_contDiffOn {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) :
    ContDiffOn ℝ ∞ (metricPBundle g) (stateBaseDomain U) := by
  have h0 : ContDiffOn ℝ ∞ (fun w => g (statePoint w)) (stateBaseDomain U) := by
    apply contDiffOn_pi.mpr
    intro i
    apply contDiffOn_pi.mpr
    intro j
    exact (hg.1 i j).comp statePoint_contDiff.contDiffOn (fun w hw => hw)
  have h1 : ContDiffOn ℝ ∞
      (fun w d i j => coordPartial d (fun p => g p i j) (statePoint w)) (stateBaseDomain U) := by
    apply contDiffOn_pi.mpr
    intro d
    apply contDiffOn_pi.mpr
    intro i
    apply contDiffOn_pi.mpr
    intro j
    exact (partial_contDiffOn (hg.1 i j) hU d).comp statePoint_contDiff.contDiffOn (fun w hw => hw)
  have h2 : ContDiffOn ℝ ∞
      (fun w d e i j => coordPartial d (coordPartial e (fun p => g p i j)) (statePoint w))
      (stateBaseDomain U) := by
    apply contDiffOn_pi.mpr
    intro d
    apply contDiffOn_pi.mpr
    intro e
    apply contDiffOn_pi.mpr
    intro i
    apply contDiffOn_pi.mpr
    intro j
    exact (partial_contDiffOn (partial_contDiffOn (hg.1 i j) hU e) hU d).comp
      statePoint_contDiff.contDiffOn (fun w hw => hw)
  exact h0.prodMk (h1.prodMk (h2.prodMk contDiffOn_id))

theorem metricPBundle_positive_jet_bound {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {w : DarbouxState}
    (hw : statePoint w ∈ U) {N : ℕ} {G : ℝ} (hG : 0 ≤ G)
    (hgB : ∀ i j k, k ≤ N + 2 →
      ‖iteratedFDeriv ℝ k (fun p => g p i j) (statePoint w)‖ ≤ G)
    {n : ℕ} (hn : 1 ≤ n) (hnN : n ≤ N) :
    ‖iteratedFDeriv ℝ n (metricPBundle g) w‖ ≤ max 1 G := by
  have hB := (metricPBundle_contDiffOn hg hU).contDiffAt
    ((stateBaseDomain_isOpen hU).mem_nhds hw)
  have h0 := hB.fst
  have h1 := hB.snd.fst
  have h2 := hB.snd.snd.fst
  have hId := hB.snd.snd.snd
  have hcon {f : Coord → ℝ} (hf : ContDiffOn ℝ ∞ f U) :
      ‖iteratedFDeriv ℝ n (fun v => f (statePoint v)) w‖ ≤
        ‖iteratedFDeriv ℝ n f (statePoint w)‖ := by
    exact norm_iteratedFDeriv_comp_statePoint hf hU hw n
  have hb0 : ‖iteratedFDeriv ℝ n (fun v => g (statePoint v)) w‖ ≤ G := by
    apply norm_iteratedFDeriv_pi_le h0 n hG
    intro i
    apply norm_iteratedFDeriv_pi_le ((contDiffAt_pi.mp h0) i) n hG
    intro j
    exact (hcon (hg.1 i j)).trans (hgB i j n (by omega))
  have hb1 : ‖iteratedFDeriv ℝ n
      (fun v d i j => coordPartial d (fun p => g p i j) (statePoint v)) w‖ ≤ G := by
    apply norm_iteratedFDeriv_pi_le h1 n hG
    intro d
    apply norm_iteratedFDeriv_pi_le ((contDiffAt_pi.mp h1) d) n hG
    intro i
    apply norm_iteratedFDeriv_pi_le ((contDiffAt_pi.mp ((contDiffAt_pi.mp h1) d)) i) n hG
    intro j
    exact ((hcon (partial_contDiffOn (hg.1 i j) hU d)).trans
      (norm_iteratedFDeriv_coordPartial_le (hg.1 i j) hU hw d n)).trans
        (hgB i j (n + 1) (by omega))
  have hb2 : ‖iteratedFDeriv ℝ n
      (fun v d e i j => coordPartial d (coordPartial e (fun p => g p i j)) (statePoint v)) w‖ ≤ G := by
    apply norm_iteratedFDeriv_pi_le h2 n hG
    intro d
    apply norm_iteratedFDeriv_pi_le ((contDiffAt_pi.mp h2) d) n hG
    intro e
    apply norm_iteratedFDeriv_pi_le ((contDiffAt_pi.mp ((contDiffAt_pi.mp h2) d)) e) n hG
    intro i
    apply norm_iteratedFDeriv_pi_le
      ((contDiffAt_pi.mp ((contDiffAt_pi.mp ((contDiffAt_pi.mp h2) d)) e)) i) n hG
    intro j
    exact (((hcon (partial_contDiffOn (partial_contDiffOn (hg.1 i j) hU e) hU d)).trans
      (norm_iteratedFDeriv_coordPartial_le (partial_contDiffOn (hg.1 i j) hU e) hU hw d n)).trans
      (norm_iteratedFDeriv_coordPartial_le (hg.1 i j) hU hw e (n + 1))).trans
        (hgB i j (n + 1 + 1) (by omega))
  exact norm_iteratedFDeriv_prod_le h0 hB.snd n (hb0.trans (le_max_right _ _))
    (norm_iteratedFDeriv_prod_le h1 hB.snd.snd n (hb1.trans (le_max_right _ _))
      (norm_iteratedFDeriv_prod_le h2 hId n (hb2.trans (le_max_right _ _))
        ((norm_iteratedFDeriv_id_pos w hn).trans (le_max_left _ _))))

end SmoothLocal.HighEquation

end

end OAI
