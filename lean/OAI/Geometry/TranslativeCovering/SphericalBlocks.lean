import OAI.Geometry.TranslativeCovering.GeometryDimension

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology

universe u_1 u_2 u_3

namespace SphericalBlocks
open Set MeasureTheory SphericalLaw CapCost BlockGeometry BlockSets ProjectiveCaps
open scoped BigOperators

lemma uniform_lens {l u₀ u B : ℝ} (hl : 0 < l) (hu₀ : 0 ≤ u₀)
    (hu : u₀ < u) (hu1 : u < 1) (hB : 0 < B) :
    ∃ n₀ : ℕ,∀ n : ℕ,n₀ ≤ n → ∀ [NeZero n],
    ∀ (I : Type u_1) [Fintype I] [DecidableEq I],Fintype.card I ≤ n^2 →
    ∀ (e : Sphere n) (axes : I → Sphere n) (τ : I → ℝ) (d : I → I → ℝ) (t : ℝ),
    0 ≤ t → t < 1 → (∀ i,l ≤ τ i) → (∀ i,τ i ≤ u₀) →
    (∀ i j,(n:ℝ)*(angle (axes i).val (axes j).val)^2 ≤ d i j^2) →
    ∀ S : Finset I,S.Nonempty → radius d S ≤ B*Real.log n →
    ∀ a ∈ S,(∀ i ∈ S,(intensity e t).real (cap (axes a).val (τ a)) ≤
      (intensity e t).real (cap (axes i).val (τ i))) →
    Real.exp (-(3+(1/l+1/(1-u^2))+2*(1/l+1/(1-u^2))/l)*
      (1+radius d S+Real.log S.card))*min ((intensity e t).real (cap (axes a).val (τ a))) (1/2) ≤
      (intensity e t).real (⋂ i ∈ S,cap (axes i).val (τ i)) := by
  obtain ⟨n₀,hn₀⟩ := GeometryDimension.lens_threshold hl hu₀ hu hB
  refine ⟨n₀,?_⟩
  intro n hn _ I _ _ hcard e axes τ d t ht ht1 hτl hτu hd S hS hr a ha hmin
  obtain ⟨hn2,hdim,hsmall,hsq⟩ := hn₀ n hn
  have hnp : 0 < (n:ℝ) := by exact_mod_cast (show 0 < n by omega)
  apply RadiusLens.lens_at_radius e axes τ d hl hu1 hu₀ ht ht1 hτl hτu hd S hS a ha hmin hdim
  · exact (div_le_div_of_nonneg_right hr hnp.le).trans_lt hsmall
  · exact GeometryDimension.small_family hn2 hl hu₀ hB.le (Finset.one_le_card.mpr hS)
      ((Finset.card_le_univ S).trans hcard) (radius_nonneg d S) hr hsq
  · exact hu₀.trans hu.le

lemma cost_metric_lower {n : ℕ} {I : Type u_2} (axes : I → Sphere n) (s : I → ℝ) (i j : I) :
    (n:ℝ)*(angle (axes i).val (axes j).val)^2 ≤
      (costDist n (fun i => (axes i).val) s i j)^2 := by
  have h : Real.sqrt n*angle (axes i).val (axes j).val ≤
      costDist n (fun i => (axes i).val) s i j := by
    exact le_add_of_nonneg_right (Real.sqrt_nonneg _)
  have hn := Real.sq_sqrt (Nat.cast_nonneg n : (0:ℝ) ≤ n)
  have hp := pow_le_pow_left₀ (mul_nonneg (Real.sqrt_nonneg _) (angle_nonneg _ _)) h 2
  simpa only [mul_pow,hn] using hp

theorem blocks {l u₀ u H : ℝ} (hl : 0 < l) (hlu : l ≤ u₀)
    (hu : u₀ < u) (hu1 : u < 1) (hH : 1 ≤ H) :
    ∃ K C : ℝ,0 < K ∧ 0 < C ∧ ∃ n₀ : ℕ,
    ∀ n : ℕ,n₀ ≤ n → ∀ [NeZero n] [Fact (2 ≤ n)],
    ∀ (I : Type u_3) [Fintype I] [DecidableEq I] [Nonempty I], Fintype.card I ≤ n^2 →
    ∀ (e : Sphere n) (t : ℝ),0 ≤ t → t < 1 →
    ∀ (axes : I → Sphere n) (τ : I → ℝ), (∀ i,l ≤ τ i) → (∀ i,τ i ≤ u₀) →
    (∀ i,(intensity e t).real (cap (axes i).val (τ i)) ≤ H) →
    let μ := intensity e t
    let caps := fun i => cap (axes i).val (τ i)
    ∃ (P : Finpartition (Finset.univ : Finset I)) (a : Finset I → I) (E : Finset I → Set (Sphere n)),
      (∀ S ∈ P.parts,a S ∈ S ∧ (∀ i ∈ S,μ.real (caps (a S)) ≤ μ.real (caps i)) ∧
        MeasurableSet (E S) ∧ E S ⊆ common caps S ∧
        Real.exp (-K*Real.log n)*clipped μ caps (a S) ≤ μ.real (E S) ∧
        0 < μ.real (E S) ∧ μ.real (E S) ≤ 1/2) ∧
      (∑ S ∈ P.parts,-Real.log (μ.real (E S))) ≤ ∑ i,cost μ caps i+(Fintype.card I:ℝ)/10 ∧
      (∑ S ∈ P.parts,Real.log (1+(μ.real (E S))⁻¹)) ≤ C*((Fintype.card I:ℝ)+∑ i,cost μ caps i) ∧
      (∑ S ∈ P.parts,Real.log (1+∑ T ∈ P.parts.erase S,Blocks.weight μ (E S) (E T))) ≤
        C*((Fintype.card I:ℝ)+∑ i,cost μ caps i) := by
  let L := 3+(1/l+1/(1-u^2))+2*(1/l+1/(1-u^2))/l
  let k := min (l/16) ((u-u₀)/4)
  let c := min ((2*l*k/Real.pi^2)/4) (1/8)
  have hu0 : 0 ≤ u₀ := (hl.trans_le hlu).le
  have hup : 0 ≤ u := hu0.trans hu.le
  have hA : 0 ≤ 1/l+1/(1-u^2) := by
    have hh : 0 < 1-u^2 := by nlinarith only [hup,hu1]
    positivity
  have hL : 1 ≤ L := by
    dsimp [L]
    have := div_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hA) hl.le
    linarith
  have hk : 0 < k := by
    dsimp [k]
    exact lt_min (div_pos hl (by norm_num)) (div_pos (sub_pos.mpr hu) (by norm_num))
  have hc : 0 < c := lt_min (by positivity) (by norm_num)
  obtain ⟨B,K,C,hB,hK,hC,hblocks⟩ := Blocks.block_estimates hL (by linarith : 1 ≤ 4*H) hc
  obtain ⟨nL,hnL⟩ := uniform_lens hl hu0 hu hu1 hB
  obtain ⟨nD,hnD⟩ := GeometryDimension.lens_threshold hl hu0 hu hB
  have hev : ∀ᶠ n : ℕ in Filter.atTop, 1 ≤ Real.log n :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (Filter.eventually_ge_atTop 1)
  obtain ⟨nE,hnE⟩ := Filter.eventually_atTop.mp hev
  refine ⟨K,C,hK,hC,max nL (max nD nE),?_⟩
  intro n hn _ _ I _ _ _ hcard e t ht ht1 axes τ hτl hτu hraw
  dsimp only
  let μ := intensity e t
  let caps := fun i => cap (axes i).val (τ i)
  let s := cost μ caps
  let d := costDist n (fun i => (axes i).val) s
  have hlog : 1 ≤ Real.log n := hnE n ((le_max_right nD nE).trans ((le_max_right nL _).trans hn))
  have hdim := (hnD n ((le_max_left nD nE).trans ((le_max_right nL _).trans hn))).2.1
  have hnp : (0:ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hcard' : (Fintype.card I:ℝ) ≤ Real.exp (2*Real.log n) := by
    rw [show 2*Real.log n = Real.log ((n:ℝ)^2) by rw [Real.log_pow]; norm_num]
    rw [Real.exp_log (sq_pos_of_pos hnp)]
    exact_mod_cast hcard
  have hpos (i : I) : 0 < μ.real (caps i) := by
    rw [show μ.real (caps i) = (σ n).real (caps i)/(σ n).real (cap e.val t) from intensity_real e t _]
    exact div_pos (cap_real_pos (axes i) ((hτu i).trans_lt (hu.trans hu1))) (cap_real_pos e ht1)
  apply hblocks (Sphere n) I μ (Real.log n) hlog hcard' caps (fun i => cap_measurable _ _) hpos d
    (costDist_nonneg _ _ _) ?_ (costDist_comm _ _ _) (costDist_triangle _ _ _) ?_ ?_
  · intro i
    apply costDist_self
    intro j
    have hh := mem_sphere_zero_iff_norm.mp (axes j).property
    intro he
    simp only [he,norm_zero] at hh
    norm_num at hh
  · intro i j
    exact NormalizedCaps.clipped_affinity e axes τ hl hu1 ht ht1 hτl hτu hu.le
      hk.le (min_le_left _ _) (by have := min_le_right (l/16) ((u-u₀)/4); dsimp [k] at *; linarith)
      hdim hH hraw hc.le (min_le_left _ _) (min_le_right _ _) i j
  · intro S hS hr a ha hmin
    exact hnL n ((le_max_left _ _).trans hn) I hcard e axes τ d t ht ht1 hτl hτu
      (cost_metric_lower axes s) S hS hr a ha hmin

end SphericalBlocks

end OAI
