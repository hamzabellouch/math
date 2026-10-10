import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorLocalOutgoing
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorFixedContinuation
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorSplice

namespace OAI

/-! Parameter continuity of the unique outgoing solution at the matching radius. -/

open Set Filter
namespace DefocusingNLS

theorem radialExteriorCanonical_parameter_limit (n : ℕ) (ν m : ℕ → ℂ) (ν₀ m₀ : ℂ)
    (hν : Tendsto ν atTop (nhds ν₀)) (hm : Tendsto m atTop (nhds m₀))
    (hm₀ : m₀ ≠ 0) (l : ℝ) (hex : HasRadialExterior ν₀ n m₀ l) :
    (∀ᶠ i in atTop, HasRadialExterior (ν i) n (m i) l) ∧
      Tendsto (fun i => radialExteriorCanonical (ν i) n (m i) l l) atTop
        (nhds (radialExteriorCanonical ν₀ n m₀ l l)) := by
  classical
  let g := radialExteriorCanonical ν₀ n m₀ l
  obtain ⟨hgc,hgout,hgd⟩ := radialExteriorCanonical_spec hex
  obtain ⟨S,hS,hp,T,Y,hY,hYcont,hYd⟩ := exists_radialExterior_local_outgoing ν₀ m₀ n hm₀
  let y₀ : S := ⟨(ν₀,m₀),hp⟩
  let y : ℕ → S := fun i => if h : (ν i,m i) ∈ S then ⟨(ν i,m i),h⟩ else y₀
  have hmem : ∀ᶠ i in atTop, (ν i,m i) ∈ S :=
    (hν.prodMk_nhds hm).eventually (hS.mem_nhds hp)
  have hyval : ∀ᶠ i in atTop, (y i).val=(ν i,m i) := by
    filter_upwards [hmem] with i hi
    simp only [y,dite_eq_left hi]
  have hy : Tendsto y atTop (nhds y₀) := by
    apply tendsto_subtype_rng.mpr
    exact (hν.prodMk_nhds hm).congr' (hyval.mono (fun _ h => h.symm))
  let u := max l T
  have hlu : l ≤ u := le_max_left _ _
  have hTu : T ≤ u := le_max_right _ _
  have hcenter : Y y₀ u=g u := by
    apply radialExterior_outgoing_unique ν₀ n m₀ u (Y y₀) g (hY y₀).1 hgc
    · intro t ht
      exact (hYd y₀ t (hTu.trans ht)).2
    · intro t ht
      exact (hgd t (hlu.trans ht)).2
    · exact (hY y₀).2
    · exact hgout
    · exact le_rfl
  have hinit : Tendsto (fun i => Y (y i) u) atTop (nhds (g u)) := by
    rw [← hcenter]
    exact (hYcont u hTu).continuousAt.tendsto.comp hy
  obtain ⟨X,hX,hXconv,hXactual⟩ := exists_radialExterior_fixed_continuation n ν ν₀ hν
    g hgc l u hlu (fun t ht => (hgd t ht.1).1) (fun t ht => (hgd t ht.1).2)
    (fun i => Y (y i) u) hinit
  let Z := fun i => radialExteriorSplice u (X i) (Y (y i))
  have hZc (i : ℕ) : Continuous (Z i) :=
    radialExteriorSplice_continuous u (X i) (Y (y i)) (hX i).1 (hY (y i)).1 (hX i).2
  have hZout : ∀ᶠ i in atTop, HasRadialOutgoingExpansion (ν i) n (m i) (Z i) := by
    filter_upwards [hyval] with i hi
    have hout : HasRadialOutgoingExpansion (ν i) n (m i) (Y (y i)) := by
      simpa only [hi] using (hY (y i)).2
    apply hout.congr
    filter_upwards [eventually_gt_atTop u] with t ht
    simp only [Z,radialExteriorSplice,not_le.mpr ht,ite_false]
  have hZactual : ∀ᶠ i in atTop, ∀ t, l ≤ t → (Z i t).1 ≠ 0 ∧
      HasDerivAt (Z i) (radialExteriorODEField (ν i) n t (Z i t)) t := by
    filter_upwards [hyval,hXactual] with i hi hXi t ht
    have hYi : ∀ s, T ≤ s → (Y (y i) s).1 ≠ 0 ∧
        HasDerivAt (Y (y i)) (radialExteriorODEField (ν i) n s (Y (y i) s)) s := by
      intro s hs
      simpa only [hi] using hYd (y i) s hs
    refine ⟨?_,?_⟩
    · by_cases htu : t ≤ u
      · simpa only [Z,radialExteriorSplice,ite_eq_left htu] using (hXi t ⟨ht,htu⟩).1
      · simpa only [Z,radialExteriorSplice,ite_eq_right htu] using
          (hYi t (hTu.trans (not_le.mp htu).le)).1
    · exact radialExteriorSplice_hasDerivAt u t (X i) (Y (y i))
        (radialExteriorODEField (ν i) n)
        (fun htu => (hXi t ⟨ht,htu⟩).2)
        (fun hut => (hYi t (hTu.trans hut)).2) (hX i).2
  have hcan : ∀ᶠ i in atTop, HasRadialExterior (ν i) n (m i) l ∧
      radialExteriorCanonical (ν i) n (m i) l l=X i l := by
    filter_upwards [hZout,hZactual] with i hi hd
    refine ⟨⟨Z i,hZc i,hi,hd⟩,?_⟩
    rw [radialExteriorCanonical_eq (Z i) (hZc i) hi hd l le_rfl]
    simp only [Z,radialExteriorSplice,ite_eq_left hlu]
  refine ⟨hcan.mono (fun _ h => h.1),?_⟩
  exact (hXconv.tendsto_at (show l ∈ Icc l u from ⟨le_rfl,hlu⟩)).congr'
    (hcan.mono (fun _ h => h.2.symm))

theorem continuous_radialExteriorCanonical_boundary {K : Type*} [MetricSpace K]
    (n : ℕ) (ν m : K → ℂ) (hν : Continuous ν) (hm : Continuous m)
    (hm0 : ∀ x, m x ≠ 0) (l : ℝ) (hex : ∀ x, HasRadialExterior (ν x) n (m x) l) :
    Continuous (fun x => radialExteriorCanonical (ν x) n (m x) l l) := by
  apply SeqContinuous.continuous
  intro x x₀ hx
  exact (radialExteriorCanonical_parameter_limit n (fun i => ν (x i)) (fun i => m (x i))
    (ν x₀) (m x₀) (hν.continuousAt.tendsto.comp hx) (hm.continuousAt.tendsto.comp hx)
    (hm0 x₀) l (hex x₀)).2

end DefocusingNLS

end OAI
