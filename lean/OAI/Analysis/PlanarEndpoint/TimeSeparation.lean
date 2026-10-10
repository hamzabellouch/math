import OAI.Analysis.PlanarEndpoint.AlmostOrthogonal
import OAI.Analysis.PlanarEndpoint.DyadicGraph
import OAI.Analysis.PlanarEndpoint.Fourier
import OAI.Analysis.PlanarEndpoint.GraphDual
import OAI.Analysis.PlanarEndpoint.TimeTree

namespace OAI

/-! Gaussian regularization, Fourier evolution and endpoint maximal estimates. -/


noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
namespace PlanarEndpoint

lemma card_integer_neighbors {ι : Type*} [Fintype ι] (f : ι → ℤ)
    (hf : Function.Injective f) (K : ℕ) (i : ι) :
    ((Finset.univ.filter fun j => |f j-f i| ≤ (K : ℤ)).card : ℝ) ≤ 2*K+1 := by
  classical
  have hh : (Finset.univ.filter fun j => |f j-f i| ≤ (K : ℤ)).card ≤
      (Finset.Icc (f i-K) (f i+K)).card := by
    apply Finset.card_le_card_of_injOn f
    · intro j hj
      have hj' := Finset.mem_filter.mp hj |>.2
      simpa only [Finset.mem_coe, Finset.mem_Icc] using (show f i-K ≤ f j ∧ f j ≤ f i+K by
        have h := abs_le.mp hj'
        omega)
    · exact hf.injOn
  have hc : (Finset.Icc (f i-K) (f i+K)).card = 2*K+1 := by
    rw [Int.card_Icc]
    omega
  rw [hc] at hh
  exact_mod_cast hh

lemma separated_interval_points {i j K w x y : ℝ} (hw : 0 ≤ w)
    (hx : x ∈ Ico (i*w) ((i+1)*w)) (hy : y ∈ Ico (j*w) ((j+1)*w))
    (hij : K ≤ |i-j|) : (K-1)*w ≤ |x-y| := by
  rcases hx with ⟨hx0,hx1⟩
  rcases hy with ⟨hy0,hy1⟩
  rcases le_total i j with h | h
  · rw [abs_of_nonpos (sub_nonpos.mpr h)] at hij
    have hxy := neg_le_abs (x-y)
    nlinarith [mul_le_mul_of_nonneg_right hij hw]
  · rw [abs_of_nonneg (sub_nonneg.mpr h)] at hij
    have hxy := le_abs_self (x-y)
    nlinarith [mul_le_mul_of_nonneg_right hij hw]

lemma scaled_cutoff_memLp (χ : Plane → ℂ) (hχ : Continuous χ)
    (hc : HasCompactSupport χ) {N : ℝ} (hN : 0 < N) :
    MemLp (fun ξ => χ (N⁻¹ • ξ)) 2 volume := by
  apply (hχ.comp (continuous_const_smul _)).memLp_of_hasCompactSupport
  exact hc.comp_homeomorph (Homeomorph.smulOfNeZero N⁻¹ (inv_ne_zero hN.ne'))

namespace DyadicGraph

abbrev Node (n : ℕ) := ↥(TimeTree.level n)

def nodeIndex {n : ℕ} (s : Node n) : ℤ := index s.val

lemma nodeIndex_injective (n : ℕ) : Function.Injective (@nodeIndex n) := by
  intro s t h
  apply Subtype.ext
  apply index_injective
  · exact (TimeTree.mem_level _ _ |>.mp s.property).trans
      (TimeTree.mem_level _ _ |>.mp t.property).symm
  · dsimp only [nodeIndex] at h
    exact_mod_cast h

lemma width_node {n : ℕ} (s : Node n) : width s.val = ((2 : ℝ)^n)⁻¹ := by
  simp only [width, (TimeTree.mem_level _ _).mp s.property, one_div, inv_pow]

lemma interval_node {n : ℕ} (s : Node n) : interval s.val =
    Ico ((nodeIndex s : ℝ) * ((2 : ℝ)^n)⁻¹)
      (((nodeIndex s : ℝ)+1) * ((2 : ℝ)^n)⁻¹) := by
  rw [interval_eq, width_node]
  simp only [nodeIndex, Int.cast_natCast]

lemma node_interval_separation {n : ℕ} (s t : Node n) {K : ℕ}
    (hfar : ¬ |nodeIndex t-nodeIndex s| ≤ (K : ℤ))
    {x y : ℝ} (hx : x ∈ interval s.val) (hy : y ∈ interval t.val) :
    (K-1 : ℝ) * ((2 : ℝ)^n)⁻¹ ≤ |x-y| := by
  have hij : (K : ℝ) ≤ |(nodeIndex s : ℝ)-(nodeIndex t : ℝ)| := by
    rw [abs_sub_comm]
    exact_mod_cast (le_of_lt (lt_of_not_ge hfar))
  rw [interval_node] at hx hy
  exact separated_interval_points (by positivity) hx hy hij

end DyadicGraph

lemma time_kernel_bound {χ : Plane → ℂ} {c C : ℝ} (_hc : 0 < c)
    (hK : ∀ N : ℝ, 0 < N → ∀ (z : Plane) (t : ℝ), ‖z‖ ≤ c*N*|t| →
      (N^2*|t|)^4 * ‖frequencyKernel (fun ξ => χ (N⁻¹ • ξ)) z t‖ ≤ C*N^2)
    {N : ℝ} (hN : 0 < N) (z : Plane) (t : ℝ) (hz : ‖z‖ ≤ 2)
    (ht : 1 ≤ N*|t|) (htc : 2 ≤ c*N*|t|) :
    ‖frequencyKernel (fun ξ => χ (N⁻¹ • ξ)) z t‖ ≤ C/N^2 := by
  have hh := hK N hN z t (hz.trans htc)
  have hp : N ≤ N^2*|t| := by nlinarith [mul_le_mul_of_nonneg_left ht hN.le]
  have hpow := pow_le_pow_left₀ hN.le hp 4
  have hmul := mul_le_mul_of_nonneg_right hpow
    (norm_nonneg (frequencyKernel (fun ξ => χ (N⁻¹ • ξ)) z t))
  have hb := hmul.trans hh
  apply (le_div_iff₀ (sq_pos_of_pos hN)).mpr
  apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hN)).mp
  convert hb using 1 <;> ring

lemma time_separation_uniform {χ : Plane → ℂ} {c : ℝ}
    (hc : 0 < c) (hχ : ContDiff ℝ ∞ χ) (hcomp : HasCompactSupport χ)
    (hann : ∀ ξ ∈ tsupport χ, c ≤ ‖ξ‖) :
    ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧
      ∀ (n : ℕ) (μ : Measure Plane) [IsFiniteMeasure μ]
        (T : Plane → ℝ) (w : Plane → ℂ) (hT : Measurable T) (hw : Measurable w)
        (hb : ∀ x, ‖w x‖ ≤ 1) (x₀ : Plane),
        (∀ᵐ x ∂μ, ‖x-x₀‖ ≤ 1) →
        let N := (2 : ℝ)^n
        let χN := fun ξ => χ (N⁻¹ • ξ)
        let hχN := scaled_cutoff_memLp χ hχ.continuous hcomp (pow_pos (by norm_num) n)
        ‖DyadicGraph.vector χN hχN μ T w hT hw hb []‖^2 ≤
          D * (∑ s ∈ TimeTree.level n, ‖DyadicGraph.vector χN hχN μ T w hT hw hb s‖^2) +
          C / N^2 * (DyadicGraph.massTree μ T hT).mass [] ^ 2 := by
  classical
  obtain ⟨C,hC,hker⟩ := frequencyKernel_time_decay hc hχ hcomp hann 4
  obtain ⟨K,hK⟩ := exists_nat_gt (2+2/c)
  have hK1 : 1 ≤ (K : ℝ)-1 := by
    have hc' : 0 < 2/c := by positivity
    linarith
  have hKc : 2 ≤ c*((K : ℝ)-1) := by
    have hd : 2/c ≤ (K : ℝ)-1 := by linarith
    have hh := (div_le_iff₀ hc).mp hd
    nlinarith
  refine ⟨C,2*K+1,hC,by positivity,?_⟩
  intro n μ inst T w hT hw hb x₀ hμ
  dsimp only
  let N : ℝ := 2^n
  have hN : 0 < N := pow_pos (by norm_num) n
  let χN : Plane → ℂ := fun ξ => χ (N⁻¹ • ξ)
  have hχN := scaled_cutoff_memLp χ hχ.continuous hcomp hN
  let G : DyadicGraph.Node n → L2 := fun s => DyadicGraph.vector χN hχN μ T w hT hw hb s.val
  let m : DyadicGraph.Node n → ℝ := fun s => (DyadicGraph.massTree μ T hT).mass s.val
  let R : DyadicGraph.Node n → DyadicGraph.Node n → Prop := fun s t =>
    |DyadicGraph.nodeIndex t-DyadicGraph.nodeIndex s| ≤ (K : ℤ)
  have hsym : ∀ ⦃first second⦄, R first second → R second first := by
    intro first second hrelated
    dsimp [R] at *
    rwa [abs_sub_comm]
  have hm : ∀ s, 0 ≤ m s := fun s => (DyadicGraph.massTree μ T hT).nonneg s.val
  have hdegree : ∀ s, ((Finset.univ.filter (R s)).card : ℝ) ≤ 2*K+1 :=
    card_integer_neighbors DyadicGraph.nodeIndex (DyadicGraph.nodeIndex_injective n) K
  have hgood (s : DyadicGraph.Node n) :
      ∀ᵐ x ∂μ.restrict (DyadicGraph.fiber T s.val),
        T x ∈ DyadicGraph.interval s.val ∧ ‖x-x₀‖ ≤ 1 :=
    (ae_restrict_mem (DyadicGraph.fiber_measurable hT s.val)).and (ae_restrict_of_ae hμ)
  have hmass (s : DyadicGraph.Node n) :
      (μ.restrict (DyadicGraph.fiber T s.val)).real univ = m s := by
    simp only [m, DyadicGraph.massTree, measureReal_def, Measure.restrict_apply_univ]
  have hfar : ∀ s t, ¬ R s t → ‖inner ℂ (G s) (G t)‖ ≤ C/N^2*m s*m t := by
    intro s t hst
    dsimp only [G, DyadicGraph.vector]
    rw [inner_graphLp]
    have hpair := norm_graphDual_pairing_le χN (hχ.continuous.comp (continuous_const_smul _)).measurable
      hχN (μ.restrict (DyadicGraph.fiber T t.val)) (μ.restrict (DyadicGraph.fiber T s.val))
      hT hw hb (B := C/N^2)
    have hh := hpair (by
      filter_upwards [Measure.quasiMeasurePreserving_fst.ae (hgood t),
        Measure.quasiMeasurePreserving_snd.ae (hgood s)] with z hz hy
      have ht := DyadicGraph.node_interval_separation t s (by
        rw [abs_sub_comm]; exact hst) hz.1 hy.1
      have htn : (K : ℝ)-1 ≤ N*|T z.1-T z.2| := by
        have ht' := mul_le_mul_of_nonneg_left ht hN.le
        have hni : N * ((K : ℝ)-1) * N⁻¹ = (K : ℝ)-1 := by field_simp
        dsimp only [N] at hni
        nlinarith [ht']
      have hzc : ‖z.1-z.2‖ ≤ 2 := by
        calc
          _ = ‖(z.1-x₀)-(z.2-x₀)‖ := by congr 1; abel
          _ ≤ ‖z.1-x₀‖+‖z.2-x₀‖ := norm_sub_le _ _
          _ ≤ 2 := by linarith [hz.2,hy.2]
      exact time_kernel_bound hc hker hN (z.1-z.2) (T z.1-T z.2) hzc
        (hK1.trans htn) (by nlinarith [mul_le_mul_of_nonneg_left htn hc.le]))
    rw [hmass,hmass] at hh
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hh
  have hh := norm_sum_sq_le_near_far G R hsym m hm (by positivity : 0 ≤ C/N^2) hdegree hfar
  dsimp only [G,m] at hh
  have hsumsq : (∑ s : DyadicGraph.Node n,
      ‖DyadicGraph.vector χN hχN μ T w hT hw hb s.val‖^2) =
      ∑ s ∈ TimeTree.level n, ‖DyadicGraph.vector χN hχN μ T w hT hw hb s‖^2 :=
    Finset.sum_coe_sort _ (fun s => ‖DyadicGraph.vector χN hχN μ T w hT hw hb s‖^2)
  rw [hsumsq] at hh
  simp only [DyadicGraph.Node, Finset.sum_coe_sort, DyadicGraph.vector_level_sum,
    DyadicGraph.mass_level_sum] at hh
  exact hh

end PlanarEndpoint
end

end OAI
