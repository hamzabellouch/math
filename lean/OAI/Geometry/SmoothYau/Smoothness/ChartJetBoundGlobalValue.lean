import Mathlib
import OAI.Geometry.SmoothYau.Smoothness.CompactMetricInverseJets

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Function
open scoped Topology ContDiff Manifold
variable {E F M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M] [T2Space M]

omit [FiniteDimensional ℝ E] [T2Space M] in
lemma contDiffOn_chartTransition_for_jets (p q : M) :
    ContDiffOn ℝ ∞ ((chartAt E p).symm.trans (chartAt E q))
      ((chartAt E p).symm.trans (chartAt E q)).source := by
  intro y hy
  have hy' : y ∈ (chartAt E p).target ∧ (chartAt E p).symm y ∈ (chartAt E q).source := hy
  exact (contMDiffAt_iff_contDiffAt.mp
    ((contMDiffAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas q) hy'.2).comp y
      (contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas p) hy'.1))).contDiffWithinAt

theorem compact_chart_jet_transfer (p q : M) {L : Set M} (hL : IsCompact L)
    (hLp : L ⊆ (chartAt E p).source) {K : Set E} (hK : IsCompact K)
    (hKq : K ⊆ (chartAt E q).target) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (U : M → F) (f : E → F), ContDiff ℝ ∞ f →
      tsupport U ⊆ L → (∀ z ∈ (chartAt E p).target, U ((chartAt E p).symm z)=f z) →
      ∀ y ∈ K, ∀ j ≤ m, ∀ B : ℝ, 0 ≤ B →
        (∀ i ≤ j, ‖iteratedFDeriv ℝ i f (chartAt E p ((chartAt E q).symm y))‖ ≤ B) →
        ‖iteratedFDeriv ℝ j (U ∘ (chartAt E q).symm) y‖ ≤ C*B := by
  let c := chartAt E p
  let d := chartAt E q
  let T := (d.symm '' K) ∩ L
  have hT : IsCompact T := (hK.image_of_continuousOn (d.continuousOn_symm.mono hKq)).inter_right hL.isClosed
  have hTd : T ⊆ d.source := by
    rintro x ⟨⟨y,hy,rfl⟩,_⟩
    exact d.map_target (hKq hy)
  let S := d '' T
  have hS : IsCompact S := hT.image_of_continuousOn (d.continuousOn.mono hTd)
  let e := d.symm.trans c
  have hSe : S ⊆ e.source := by
    rintro y ⟨x,hx,rfl⟩
    refine ⟨d.map_source (hTd hx),?_⟩
    change d.symm (d x) ∈ c.source
    rw [d.left_inv (hTd hx)]
    exact hLp hx.2
  obtain ⟨ψ,hψ,heψ⟩ := smooth_extension_near_compact hS e.open_source hSe
    (contDiffOn_chartTransition_for_jets q p)
  obtain ⟨D,hD,hDj⟩ := compact_raw_jet_bound isOpen_univ hK (subset_univ _)
    hψ.contDiffOn m
  let C : ℝ := (m.factorial : ℝ)*D^m+1
  have hCp : 0 < C := by dsimp [C]; positivity
  refine ⟨C,hCp,?_⟩
  intro U f hf hUs hUf y hy j hj B hB hfj
  by_cases hx : d.symm y ∈ L
  · have hyS : y ∈ S := ⟨d.symm y,⟨⟨y,hy,rfl⟩,hx⟩,d.right_inv (hKq hy)⟩
    have hey := hSe hyS
    have heψy : (e : E → E) =ᶠ[𝓝 y] ψ := heψ.filter_mono (nhds_le_nhdsSet hyS)
    have heq : U ∘ d.symm =ᶠ[𝓝 y] f ∘ ψ := by
      filter_upwards [e.open_source.mem_nhds hey,heψy] with z hz hzz
      have hcz : d.symm z ∈ c.source := hz.2
      change U (d.symm z)=f (ψ z)
      rw [←hzz]
      change U (d.symm z)=f (c (d.symm z))
      rw [←hUf _ (c.map_source hcz),c.left_inv hcz]
    rw [(heq.iteratedFDeriv ℝ j).eq_of_nhds]
    have hb : ∀ i ≤ j, ‖iteratedFDeriv ℝ i f (ψ y)‖ ≤ B := by
      intro i hi
      rw [←heψy.eq_of_nhds]
      exact hfj i hi
    have hd : ∀ i, 1 ≤ i → i ≤ j → ‖iteratedFDeriv ℝ i ψ y‖ ≤ D^i := by
      intro i hi hij
      exact (hDj i (hij.trans hj) y hy).trans (by simpa using pow_le_pow_right₀ hD hi)
    have hbound := norm_iteratedFDeriv_comp_le hf hψ
      (le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top j))) y hb hd
    apply hbound.trans
    have hfact : (j.factorial : ℝ) ≤ m.factorial := by exact_mod_cast Nat.factorial_le hj
    have hp := pow_le_pow_right₀ hD hj
    have hmul := mul_le_mul hfact hp (pow_nonneg (zero_le_one.trans hD) _) (Nat.cast_nonneg _)
    calc
      _ = ((j.factorial : ℝ)*D^j)*B := by ring
      _ ≤ ((m.factorial : ℝ)*D^m)*B := mul_le_mul_of_nonneg_right hmul hB
      _ ≤ C*B := mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) hB
  · have hn : d.symm y ∉ tsupport U := fun h => hx (hUs h)
    have he : U ∘ d.symm =ᶠ[𝓝 y] (fun _ => (0:F)) :=
      (notMem_tsupport_iff_eventuallyEq.mp hn).comp_tendsto (d.continuousAt_symm (hKq hy)).tendsto
    rw [(he.iteratedFDeriv ℝ j).eq_of_nhds]
    simpa using mul_nonneg hCp.le hB


end

open Set Filter Function Manifold
open scoped Topology ContDiff
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [T2Space M] [CompactSpace M]
namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2*(2*(k:ℝ))}
  (A : CompactMetricAtlas g k hs)

omit [T2Space M] [CompactSpace M] in
lemma chartJetBound_global_value {m : ℕ} {u : M → ℂ} {B : ℝ}
    (hB : 0 ≤ B) (hj : A.ChartJetBound m u B) (x : M) :
    ‖u x‖ ≤ (Fintype.card A.t:ℝ)*B := by
  classical
  have hb (i : A.t) : ‖A.η i x*u x‖ ≤ B := by
    by_cases hx : x ∈ tsupport (A.η i)
    · have hxs := A.chart_η i hx
      have h := hj i 0 (Nat.zero_le _) (chartAt E (A.p i) x)
      simpa only [norm_iteratedFDeriv_zero,chartLocalize_eq _ _ _ ((chartAt E (A.p i)).map_source hxs),
        (chartAt E (A.p i)).left_inv hxs] using h
    · rw [image_eq_zero_of_notMem_tsupport hx,zero_mul,norm_zero]
      exact hB
  calc
    ‖u x‖ = ‖∑ i : A.t, A.η i x*u x‖ := by rw [←Finset.sum_mul,A.sum_η,one_mul]
    _ ≤ ∑ i : A.t, ‖A.η i x*u x‖ := norm_sum_le _ _
    _ ≤ ∑ _i : A.t, B := Finset.sum_le_sum (fun i _ => hb i)
    _ = _ := by simp

theorem chartJetBound_controls_compact_raw (q : M) {K : Set E}
    (hK : IsCompact K) (hKt : K ⊆ (chartAt E q).target) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : M → ℂ), ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℂ) ∞ u →
      ∀ B : ℝ, 0 ≤ B → A.ChartJetBound m u B →
      ∀ y ∈ K, ∀ j ≤ m, ‖iteratedFDeriv ℝ j (u ∘ (chartAt E q).symm) y‖ ≤ C*B := by
  classical
  choose Cs hCs htrans using fun i : A.t => compact_chart_jet_transfer (F := ℂ) (A.p i) q
    (HasCompactSupport.of_compactSpace (A.η i)) (A.chart_η i) hK hKt m
  let C : ℝ := 1+∑ i : A.t, Cs i
  have hC : 0 < C := by
    have hsum : 0 ≤ ∑ i : A.t, Cs i := Finset.sum_nonneg (fun i _ => (hCs i).le)
    exact add_pos_of_pos_of_nonneg zero_lt_one hsum
  refine ⟨C,hC,?_⟩
  intro u hu B hB hjet y hy j hj
  let U : A.t → M → ℂ := fun i x => A.η i x*u x
  have hU (i : A.t) : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℂ) ∞ (U i) := contMDiff_complex_mul (A.smooth_η i) hu
  have hsum : u ∘ (chartAt E q).symm=fun z => ∑ i : A.t, U i ((chartAt E q).symm z) := by
    funext z
    simp only [U,←Finset.sum_mul,A.sum_η,one_mul,Function.comp_apply]
  have hdiff (i : A.t) : ContDiffAt ℝ j (U i ∘ (chartAt E q).symm) y :=
    (contMDiffAt_iff_contDiffAt.mp ((hU i).contMDiffAt.comp y
      (contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas q) (hKt hy)))).of_le
        (le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top j)))
  have hbound (i : A.t) :
      ‖iteratedFDeriv ℝ j (U i ∘ (chartAt E q).symm) y‖ ≤ Cs i*B := by
    apply htrans i (U i) (chartLocalize (E := E) (A.p i) (A.η i) u)
      (contDiff_chartLocalize _ _ _ (HasCompactSupport.of_compactSpace _) (A.chart_η i) (A.smooth_η i) hu)
      tsupport_mul_subset_left
      (fun z hz => (chartLocalize_eq _ _ _ hz).symm) y hy j hj B hB
    intro l hl
    exact hjet i l (hl.trans hj) _
  rw [hsum]
  have hej := iteratedFDeriv_fun_sum_apply (u := Finset.univ) (fun i _ => hdiff i)
  simp only [Function.comp_apply] at hej
  rw [hej]
  calc
    _ ≤ ∑ i : A.t, ‖iteratedFDeriv ℝ j (U i ∘ (chartAt E q).symm) y‖ := norm_sum_le _ _
    _ ≤ ∑ i : A.t, Cs i*B := Finset.sum_le_sum (fun i _ => hbound i)
    _ = (∑ i : A.t, Cs i)*B := (Finset.sum_mul ..).symm
    _ ≤ C*B := mul_le_mul_of_nonneg_right (by change (∑ i : A.t, Cs i) ≤ 1+∑ i : A.t, Cs i; linarith) hB

theorem chartJetBound_controls_real_compact_raw (q : M) {K : Set E}
    (hK : IsCompact K) (hKt : K ⊆ (chartAt E q).target) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : M → ℝ), ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ u →
      ∀ B : ℝ, 0 ≤ B → A.ChartJetBound m (fun x => (u x:ℂ)) B →
      ∀ y ∈ K, ∀ j ≤ m, ‖iteratedFDeriv ℝ j (u ∘ (chartAt E q).symm) y‖ ≤ C*B := by
  obtain ⟨C,hC,hj⟩ := A.chartJetBound_controls_compact_raw q hK hKt m
  refine ⟨C,hC,?_⟩
  intro u hu B hB hjet y hy j hjm
  have hu' : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℂ) ∞ (fun x => (u x:ℂ)) :=
    Complex.ofRealCLM.contMDiff.comp hu
  have hh := hj _ hu' B hB hjet y hy j hjm
  have hd : ContDiffAt ℝ ∞ (u ∘ (chartAt E q).symm) y :=
    contMDiffAt_iff_contDiffAt.mp (hu.contMDiffAt.comp y
      (contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas q) (hKt hy)))
  change ‖iteratedFDeriv ℝ j (Complex.ofRealLI ∘ (u ∘ (chartAt E q).symm)) y‖ ≤ C*B at hh
  rw [Complex.ofRealLI.norm_iteratedFDeriv_comp_left hd
    (le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top j)))] at hh
  exact hh

theorem chartJetBound_controls_finite_real_raw (tests : List (CoordinateTest E M)) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : M → ℝ), ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ u →
      ∀ B : ℝ, 0 ≤ B → A.ChartJetBound m (fun x => (u x:ℂ)) B →
      ∀ t ∈ tests, ∀ y ∈ t.compactSet, ∀ j ≤ m,
        ‖iteratedFDeriv ℝ j (u ∘ (chartAt E t.center).symm) y‖ ≤ C*B := by
  classical
  choose Cs hCs hJ using fun t : CoordinateTest E M =>
    A.chartJetBound_controls_real_compact_raw t.center t.isCompact t.inTarget m
  let C := 1+∑ t ∈ tests.toFinset, Cs t
  have hC : 0 < C := by
    have hh : 0 ≤ ∑ t ∈ tests.toFinset, Cs t := Finset.sum_nonneg (fun t _ => (hCs t).le)
    dsimp [C]; linarith
  refine ⟨C,hC,?_⟩
  intro u hu B hB hjet t ht y hy j hj
  apply (hJ t u hu B hB hjet y hy j hj).trans
  apply mul_le_mul_of_nonneg_right _ hB
  have hh := Finset.single_le_sum (fun t (_ : t ∈ tests.toFinset) => (hCs t).le)
    (List.mem_toFinset.mpr ht)
  dsimp [C]; linarith
end CompactMetricAtlas

end YauCounterexamples
end

end OAI
