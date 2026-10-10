import OAI.Combinatorics.TreewidthL1.TreeGeometry

namespace OAI

namespace BoundedTreewidthL1.NoiseCube
open MeasureTheory Set
open scoped unitInterval ENNReal
attribute [local instance] Classical.decEq Classical.propDecidable
theorem affine_interval_bound (A b t : ℝ) (hb : b ≠ 0) :
    volume {x : ℝ | |A + b*x| < t} = ENNReal.ofReal (2*t/|b|) := by
  have hset : {x : ℝ | |A + b*x| < t} =
      (fun x : ℝ => b*x) ⁻¹' Ioo (-t-A) (t-A) := by
    ext x
    simp only [mem_ofPred_eq, mem_preimage, mem_Ioo, abs_lt]
    constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> linarith
  rw [hset, Real.volume_preimage_mul_left hb, Real.volume_Ioo,
    ← ENNReal.ofReal_mul (abs_nonneg _)]
  congr 1
  rw [abs_inv]
  ring

lemma unit_affine_bound (A b t β : ℝ) (ht : 0 ≤ t) (hβ : 0 < β) (hb : β ≤ |b|) :
    volume {u : I | |A+b*(u:ℝ)| < t} ≤ ENNReal.ofReal (2*t/β) := by
  have hbn : b ≠ 0 := by intro he; simp [he] at hb; linarith
  have hm : MeasurableSet {u : ℝ | |A+b*u| < t} := measurableSet_lt (by fun_prop) measurable_const
  have he := unitInterval.measurePreserving_coe.measure_preimage hm.nullMeasurableSet
  change volume (Subtype.val ⁻¹' {u : ℝ | |A+b*u| < t}) ≤ _
  rw [he]
  apply (Measure.restrict_le_self _).trans
  rw [affine_interval_bound A b t hbn]
  exact ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_left (by positivity) hβ hb)

lemma cube_strip {m : ℕ} (j : Fin (m+1)) (c : Fin (m+1) → ℝ)
    (A t γ : ℝ) (ht : 0 ≤ t) (hγ : 0 < γ) (hc : γ ≤ |c j|) :
    volume {U : Fin (m+1) → I | |A+∑ i, (U i:ℝ)*c i| < t} ≤ ENNReal.ofReal (2*t/γ) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m+1) => I) j
  let E : Set (I × (Fin m → I)) := {z | |A+(z.1:ℝ)*c j+∑ i, (z.2 i:ℝ)*c (j.succAbove i)| < t}
  have he : {U : Fin (m+1) → I | |A+∑ i, (U i:ℝ)*c i| < t} = e ⁻¹' E := by
    ext U
    simp only [E,mem_ofPred_eq,mem_preimage]
    have hh := Fin.sum_univ_succAbove (fun i => (U i:ℝ)*c i) j
    change (|A+∑ i, (U i:ℝ)*c i| < t) ↔
      (|A+(U j:ℝ)*c j+∑ i, (U (j.succAbove i):ℝ)*c (j.succAbove i)| < t)
    rw [hh, add_assoc]
  rw [he,(volume_preserving_piFinSuccAbove (fun _ : Fin (m+1) => I) j).measure_preimage_equiv E]
  change (volume.prod volume) E ≤ _
  rw [Measure.prod_apply_symm (measurableSet_lt (by fun_prop) measurable_const)]
  calc
    _ ≤ ∫⁻ U : Fin m → I, ENNReal.ofReal (2*t/γ) := by
      apply lintegral_mono
      intro U
      have hs : (fun u : I => (u,U)) ⁻¹' E =
          {u : I | |(A+∑ i, (U i:ℝ)*c (j.succAbove i)) + c j*(u:ℝ)| < t} := by
        ext u
        simp only [E, mem_preimage, mem_ofPred_eq]
        ring_nf
      dsimp only
      rw [hs]
      exact unit_affine_bound (A+∑ i, (U i:ℝ)*c (j.succAbove i)) (c j) t γ ht hγ hc
    _ = _ := by simp

lemma cube_strip_any {m : ℕ} (j : Fin m) (c : Fin m → ℝ)
    (A t γ : ℝ) (ht : 0 ≤ t) (hγ : 0 < γ) (hc : γ ≤ |c j|) :
    volume {U : Fin m → I | |A+∑ i, (U i:ℝ)*c i| < t} ≤ ENNReal.ofReal (2*t/γ) := by
  cases m with
  | zero => exact j.elim0
  | succ m => exact cube_strip j c A t γ ht hγ hc

lemma product_strip_first {m : ℕ} (A b t β : ℝ) (c : Fin m → ℝ)
    (ht : 0 ≤ t) (hβ : 0 < β) (hb : β ≤ |b|) :
    (volume.prod volume) {z : I × (Fin m → I) |
      |A+b*(1+(z.1:ℝ))+∑ i, (z.2 i:ℝ)*c i| < t} ≤ ENNReal.ofReal (2*t/β) := by
  rw [Measure.prod_apply_symm (measurableSet_lt (by fun_prop) measurable_const)]
  calc
    _ ≤ ∫⁻ U : Fin m → I, ENNReal.ofReal (2*t/β) := by
      apply lintegral_mono
      intro U
      have hs : (fun u : I => (u,U)) ⁻¹'
          {z : I × (Fin m → I) | |A+b*(1+(z.1:ℝ))+∑ i, (z.2 i:ℝ)*c i| < t} =
          {u : I | |(A+b+∑ i, (U i:ℝ)*c i) + b*(u:ℝ)| < t} := by
        ext u
        simp only [mem_preimage, mem_ofPred_eq]
        ring_nf
      dsimp only
      rw [hs]
      exact unit_affine_bound (A+b+∑ i, (U i:ℝ)*c i) b t β ht hβ hb
    _ = _ := by simp

lemma product_strip_second {m : ℕ} (j : Fin m) (A b t γ : ℝ) (c : Fin m → ℝ)
    (ht : 0 ≤ t) (hγ : 0 < γ) (hc : γ ≤ |c j|) :
    (volume.prod volume) {z : I × (Fin m → I) |
      |A+b*(1+(z.1:ℝ))+∑ i, (z.2 i:ℝ)*c i| < t} ≤ ENNReal.ofReal (2*t/γ) := by
  rw [Measure.prod_apply (measurableSet_lt (by fun_prop) measurable_const)]
  calc
    _ ≤ ∫⁻ u : I, ENNReal.ofReal (2*t/γ) := by
      apply lintegral_mono
      intro u
      exact cube_strip_any j c (A+b*(1+(u:ℝ))) t γ ht hγ hc
    _ = _ := by simp
theorem simultaneous_gap {S : Type*} [Fintype S]
    (m : ℕ) (A b : S → ℝ) (c : S → Fin m → ℝ) (t β γ : ℝ) (ht : 0 ≤ t)
    (hβ : 0 < β) (hγ : 0 < γ)
    (hamp : ∀ s, β ≤ |b s| ∨ ∃ j, γ ≤ |c s j|)
    (hbudget : (Fintype.card S : ℝ) * (2*t/β + 2*t/γ) ≤ 1/2) :
    ENNReal.ofReal (1/2 : ℝ) ≤
      (volume.prod volume) {z : I × (Fin m → I) | ∀ s, t ≤ |A s + b s * (1+(z.1:ℝ)) + ∑ i, (z.2 i:ℝ)*c s i|} := by
  classical
  let E : Set (I × (Fin m → I)) := ⋃ s, {z : I × (Fin m → I) | |A s + b s*(1+(z.1:ℝ))+∑ i, (z.2 i:ℝ)*c s i| < t}
  have hE : MeasurableSet E := MeasurableSet.iUnion fun s => measurableSet_lt (by fun_prop) measurable_const
  have hnonneg : 0 ≤ 2*t/β + 2*t/γ := by positivity
  have hmass : (volume.prod volume) E ≤ ENNReal.ofReal (1/2 : ℝ) := by
    calc
      _ ≤ ∑ s, (volume.prod volume) ({z : I × (Fin m → I) | |A s + b s*(1+(z.1:ℝ))+∑ i, (z.2 i:ℝ)*c s i| < t}) := measure_iUnion_fintype_le _ _
      _ ≤ ∑ _s : S, ENNReal.ofReal (2*t/β + 2*t/γ) := by
        apply Finset.sum_le_sum
        intro s _
        rcases hamp s with h | h
        · exact (product_strip_first _ _ _ _ _ ht hβ h).trans
            (ENNReal.ofReal_le_ofReal (le_add_of_nonneg_right (by positivity)))
        · obtain ⟨j,hj⟩ := h
          exact (product_strip_second j _ _ _ _ _ ht hγ hj).trans
            (ENNReal.ofReal_le_ofReal (le_add_of_nonneg_left (by positivity)))
      _ = ENNReal.ofReal ((Fintype.card S : ℝ)*(2*t/β + 2*t/γ)) := by
        simp [ENNReal.ofReal_mul]
      _ ≤ _ := ENNReal.ofReal_le_ofReal hbudget
  have hfin : (volume.prod volume) E ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hmass
  have hgood : {z : I × (Fin m → I) | ∀ s, t ≤ |A s + b s * (1+(z.1:ℝ)) + ∑ i, (z.2 i:ℝ)*c s i|} = Eᶜ := by
    ext z
    simp [E]
  rw [hgood, measure_compl hE hfin]
  simp only [measure_univ]
  apply ENNReal.le_sub_of_add_le_right hfin
  calc
    _ ≤ ENNReal.ofReal (1/2 : ℝ) + ENNReal.ofReal (1/2 : ℝ) := add_le_add_right hmass _
    _ = 1 := by rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]; norm_num

end BoundedTreewidthL1.NoiseCube

namespace BoundedTreewidthL1.RootedTree
attribute [local instance] Classical.decEq Classical.propDecidable
variable {I : Type*} (T : SimpleGraph I) (hT : T.IsTree) (root X Y : I)
lemma join_prefix_data (s : ℕ)
    (_ : s ≤ (forest T hT root).depth X) (hsy : s ≤ (forest T hT root).depth Y)
    (hs : (downPath T hT root X).getVert s = (downPath T hT root Y).getVert s)
    (hmax : ∀ a b, a ≤ (forest T hT root).depth X → b ≤ (forest T hT root).depth Y →
      (downPath T hT root X).getVert a = (downPath T hT root Y).getVert b → a = b ∧ a ≤ s)
    (e : ℕ) (hse : s ≤ e) (hex : e ≤ (forest T hT root).depth X) :
    let v := (downPath T hT root X).getVert
    let l := (forest T hT root).depth Y-s
    (forest T hT Y).depth (v e) = l+(e-s) ∧
    ∀ b, s ≤ b → b ≤ e → (downPath T hT Y (v e)).getVert (l+(b-s)) = v b := by
  dsimp only
  have hedepth := depth_getVert T hT root X e hex
  have hpref (b : ℕ) (hb : b ≤ e) :
      (downPath T hT root ((downPath T hT root X).getVert e)).getVert b =
        (downPath T hT root X).getVert b := by
    rw [downPath_take,SimpleGraph.Walk.take_getVert,inf_eq_right.mpr hb]
  have hse' : s ≤ (forest T hT root).depth ((downPath T hT root X).getVert e) := by omega
  have hs' : (downPath T hT root ((downPath T hT root X).getVert e)).getVert s =
      (downPath T hT root Y).getVert s := (hpref s hse).trans hs
  have hm : ∀ a b, a ≤ (forest T hT root).depth ((downPath T hT root X).getVert e) →
      b ≤ (forest T hT root).depth Y →
      (downPath T hT root ((downPath T hT root X).getVert e)).getVert a =
        (downPath T hT root Y).getVert b → a = b ∧ a ≤ s := by
    intro a b ha hb he
    rw [hedepth] at ha
    rw [hpref a ha] at he
    exact hmax a b (ha.trans hex) hb he
  constructor
  · simpa only [hedepth] using join_length T hT root ((downPath T hT root X).getVert e) Y s hse' hsy hs' hm
  · intro b hsb hbe
    have hh := join_suffix T hT root ((downPath T hT root X).getVert e) Y s hse' hsy hs' hm (b-s)
    rw [Nat.add_sub_of_le hsb,hpref b hbe] at hh
    exact hh
end BoundedTreewidthL1.RootedTree

namespace BoundedTreewidthL1.ExpandedConstruction.TreeData
open _root_.OAI.BoundedTreewidthL1.RootedTree
attribute [local instance] Classical.decEq Classical.propDecidable
variable {I V ι : Type*} [Fintype I] [Fintype V] [Fintype ι]
  {T : SimpleGraph I} {M : ℝ} (D : TreeData (V := V) (ι := ι) T M)

lemma height_segment (hT : T.IsTree) (hM : 0 < M) (hι : 0 < Fintype.card ι)
    (Y Z : I) (y z : V) (hy : y ∈ D.B Y) (hz : z ∈ D.B Z)
    (v : ℕ → I) (s e l t : ℕ) (hst : s ≤ t) (hte : t < e)
    (hlen : (forest T hT Y).depth Z = l+(e-s))
    (hpath : ∀ b, s ≤ b → b ≤ e → (downPath T hT Y Z).getVert (l+(b-s)) = v b)
    (hpar : ∀ b, t ≤ b → b < e → D.parent (v (b+1)) = some (v b))
    (r : ι) (hfixed : ∀ b, t ≤ b → b ≤ e → D.F (v b) r = D.F (v t) r)
    (hkeep : ∀ b, t ≤ b → b < e → r ∈ D.C (v (b+1)) ∧ r ≠ D.fresh₁ (v b) ∧ r ≠ D.fresh₂ (v b))
    (hF : ∀ x, -M ≤ D.F (v t) r x ∧ D.F (v t) r x ≤ M)
    (ε : ℝ) (hlo : ε ≤ D.F (v t) r z+M) (hhi : ε ≤ M-D.F (v t) r z)
    (hgap : ∀ x ∈ D.B (v t), ε ≤ |D.F (v t) r z-D.F (v t) r x|) :
    ε/2 ≤ D.dist y z := by
  have hp (b : ℕ) (hb : l ≤ b) (hbe : b ≤ l+(e-s)) :
      (downPath T hT Y Z).getVert b = v (s+(b-l)) := by
    have hh := hpath (s+(b-l)) (by omega) (by omega)
    simpa only [show l+(s+(b-l)-s) = b by omega] using hh
  have htpath := hpath t hst hte.le
  apply D.height_test hT hM hι Y Z y z hy hz (l+(t-s)) (by omega) r
  · intro b htb hbe
    rw [hp b (by omega) (by omega),hp (b+1) (by omega) (by omega)]
    simpa only [show s+(b+1-l) = (s+(b-l))+1 by omega] using hpar (s+(b-l)) (by omega) (by omega)
  · intro b htb hbe
    rw [hp b (by omega) (by omega),htpath]
    exact hfixed _ (by omega) (by omega)
  · intro b htb hbe
    rw [hp b (by omega) (by omega),hp (b+1) (by omega) (by omega)]
    simpa only [show s+(b+1-l) = (s+(b-l))+1 by omega] using hkeep (s+(b-l)) (by omega) (by omega)
  · simpa only [htpath] using hF
  · simpa only [htpath] using hlo
  · simpa only [htpath] using hhi
  · simpa only [htpath] using hgap

lemma launch_segment (hT : T.IsTree) (hM : 0 < M) (hι : 0 < Fintype.card ι)
    (Y Z : I) (y z : V) (hy : y ∈ D.B Y) (hz : z ∈ D.B Z)
    (v : ℕ → I) (s e l t : ℕ) (hst : s ≤ t) (hte : t < e)
    (hlen : (forest T hT Y).depth Z = l+(e-s))
    (hpath : ∀ b, s ≤ b → b ≤ e → (downPath T hT Y Z).getVert (l+(b-s)) = v b)
    (hpar : ∀ b, t ≤ b → b < e → D.parent (v (b+1)) = some (v b))
    (hij : D.fresh₁ (v t) ≠ D.fresh₂ (v t))
    (hbag : ∀ x ∈ D.B (v t), D.F (v t) (D.fresh₁ (v t)) x = D.F (v t) (D.fresh₂ (v t)) x)
    (hfixed : ∀ r ∈ ({D.fresh₁ (v t),D.fresh₂ (v t)} : Finset ι), ∀ b, t ≤ b → b ≤ e → D.F (v b) r = D.F (v t) r)
    (hinit : D.fresh₁ (v t) ∈ D.C (v (t+1)) ∧ D.fresh₂ (v t) ∈ D.C (v (t+1)))
    (hkeep : ∀ r ∈ ({D.fresh₁ (v t),D.fresh₂ (v t)} : Finset ι), ∀ b, t+1 ≤ b → b < e →
      r ∈ D.C (v (b+1)) ∧ r ≠ D.fresh₁ (v b) ∧ r ≠ D.fresh₂ (v b))
    (hF : ∀ r ∈ ({D.fresh₁ (v t),D.fresh₂ (v t)} : Finset ι), ∀ x, -M ≤ D.F (v t) r x ∧ D.F (v t) r x ≤ M) :
    |D.F (v t) (D.fresh₁ (v t)) z-D.F (v t) (D.fresh₂ (v t)) z|/2 ≤ D.dist y z := by
  have hp (b : ℕ) (hb : l ≤ b) (hbe : b ≤ l+(e-s)) :
      (downPath T hT Y Z).getVert b = v (s+(b-l)) := by
    have hh := hpath (s+(b-l)) (by omega) (by omega)
    simpa only [show l+(s+(b-l)-s) = b by omega] using hh
  have htpath := hpath t hst hte.le
  rw [← htpath]
  apply D.launch_test hT hM hι Y Z y z hy hz (l+(t-s)) (by omega)
  · intro b htb hbe
    rw [hp b (by omega) (by omega),hp (b+1) (by omega) (by omega)]
    simpa only [show s+(b+1-l) = (s+(b-l))+1 by omega] using hpar (s+(b-l)) (by omega) (by omega)
  · simpa only [htpath] using hij
  · simpa only [htpath] using hbag
  · rw [htpath]
    intro r hr b htb hbe
    rw [hp b (by omega) (by omega)]
    exact hfixed r hr _ (by omega) (by omega)
  · simpa only [htpath,show l+(t-s)+1 = l+(t+1-s) by omega,hpath (t+1) (by omega) (by omega)] using hinit
  · rw [htpath]
    intro r hr b htb hbe
    rw [hp b (by omega) (by omega),hp (b+1) (by omega) (by omega)]
    simpa only [show s+(b+1-l) = (s+(b-l))+1 by omega] using hkeep r hr (s+(b-l)) (by omega) (by omega)
  · simpa only [htpath] using hF
end BoundedTreewidthL1.ExpandedConstruction.TreeData

namespace BoundedTreewidthL1.NoiseCube
open MeasureTheory Set LaunchNoise
open scoped unitInterval ENNReal
attribute [local instance] Classical.decEq Classical.propDecidable
lemma flip_triple {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    (μ : Measure A) (ν : Measure B) (κ : Measure C) [SFinite μ] [SFinite ν] [SFinite κ] :
    MeasurePreserving (fun z : A × (B × C) => (z.2.1,(z.1,z.2.2)))
      (μ.prod (ν.prod κ)) (ν.prod (μ.prod κ)) := by
  have h₁ := (measurePreserving_prodAssoc μ ν κ).symm
  have h₂ := (Measure.measurePreserving_swap (μ := μ) (ν := ν)).prod (MeasurePreserving.id κ)
  have h₃ := measurePreserving_prodAssoc ν μ κ
  exact h₃.comp (h₂.comp h₁)

lemma conditioned_gap {S : Type*} [Fintype S] {n m : ℕ}
    (μ : Fin n → ℝ) (_ : ∀ a, 0 ≤ μ a) (_ : ∑ a, μ a = 1)
    (A b : S → ℝ) (c : Fin n → S → Fin m → ℝ) (E : Set (Fin n))
    (t β γ ρ : ℝ) (ht : 0 ≤ t) (hβ : 0 < β) (hγ : 0 < γ) (_ : 0 ≤ ρ)
    (hgood : ENNReal.ofReal ρ ≤ locationLaw μ E)
    (hamp : ∀ a ∈ E, ∀ s, β ≤ |b s| ∨ ∃ j, γ ≤ |c a s j|)
    (hbudget : (Fintype.card S : ℝ)*(2*t/β+2*t/γ) ≤ 1/2) :
    ENNReal.ofReal (ρ/2) ≤ noiseLaw m μ {ω | ∀ s,
      t ≤ |A s+b s*noiseXi ω+∑ j, (ω.2.2 j:ℝ)*c ω.2.1 s j|} := by
  let Q : Set (Fin n × (I × (Fin m → I))) := {z | ∀ s,
    t ≤ |A s+b s*(1+(z.2.1:ℝ))+∑ j, (z.2.2 j:ℝ)*c z.1 s j|}
  have hQ : MeasurableSet Q := by
    dsimp only [Q]
    simp_rw [ofPred_forall]
    apply MeasurableSet.iInter
    intro s
    apply measurableSet_le measurable_const
    apply Measurable.abs
    fun_prop
  have he : {ω : NoiseSpace n m | ∀ s,
      t ≤ |A s+b s*noiseXi ω+∑ j, (ω.2.2 j:ℝ)*c ω.2.1 s j|} =
      (fun z : I × (Fin n × (Fin m → I)) => (z.2.1,(z.1,z.2.2))) ⁻¹' Q := rfl
  rw [he,noiseLaw,(flip_triple volume (locationLaw μ) volume).measure_preimage hQ.nullMeasurableSet]
  rw [Measure.prod_apply hQ]
  calc
    ENNReal.ofReal (ρ/2) = ENNReal.ofReal (1/2 : ℝ)*ENNReal.ofReal ρ := by
      rw [← ENNReal.ofReal_mul (by norm_num)]; congr 1; ring
    _ ≤ ENNReal.ofReal (1/2 : ℝ)*locationLaw μ E := mul_le_mul_right hgood _
    _ = ∫⁻ a, E.indicator (fun _ => ENNReal.ofReal (1/2 : ℝ)) a ∂locationLaw μ :=
      (lintegral_indicator_const MeasurableSet.of_discrete _).symm
    _ ≤ _ := by
      apply lintegral_mono
      intro a
      by_cases ha : a ∈ E
      · rw [Set.indicator_of_mem ha]
        exact simultaneous_gap m A b (c a) t β γ ht hβ hγ (hamp a ha) hbudget
      · simp only [Set.indicator_of_notMem ha]; exact bot_le

lemma pi_conditioned {n : ℕ} {Ω : Fin (n+1) → Type*}
    [∀ i, MeasurableSpace (Ω i)] (μ : ∀ i, Measure (Ω i)) [∀ i, IsProbabilityMeasure (μ i)]
    (a : Fin (n+1)) (E : Set (∀ i, Ω i)) (hE : MeasurableSet E) (p : ℝ≥0∞)
    (hfiber : ∀ rest : ∀ j : Fin n, Ω (a.succAbove j),
      p ≤ μ a {u | Fin.insertNth a u rest ∈ E}) : p ≤ Measure.pi μ E := by
  let e := MeasurableEquiv.piFinSuccAbove Ω a
  have he := (measurePreserving_piFinSuccAbove μ a).symm.measure_preimage_equiv E
  rw [← he,Measure.prod_apply_symm (e.symm.measurable hE)]
  calc
    p = ∫⁻ rest : ∀ j : Fin n, Ω (a.succAbove j), p ∂Measure.pi (fun j => μ (a.succAbove j)) := by simp
    _ ≤ _ := lintegral_mono (fun rest => hfiber rest)
end BoundedTreewidthL1.NoiseCube

end OAI
