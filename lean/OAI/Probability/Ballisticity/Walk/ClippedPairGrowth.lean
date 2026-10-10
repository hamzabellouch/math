import Mathlib
import OAI.Probability.Ballisticity.Estimates.UniformLowerMass

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience
noncomputable def centralPrefixMass {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (θ z : ℝ) (H : ℕ) (ω : Environment d) (x : Lattice d) : ℝ :=
  (quenchedKernel (ω,x)).real (TubePrefix ℓ f x θ z H)
noncomputable def jumpPrefixMass {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (b a s : ℝ) (H : ℕ) (ω : Environment d) (x : Lattice d) : ℝ :=
  (quenchedKernel (ω,x)).real (EndpointPrefix ℓ x H {z | a < s*(signedCoordinate f (z-x)-b)})
lemma centralPrefixMass_measurable {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (θ z : ℝ) (H : ℕ) : Measurable (fun p : Environment d × Lattice d =>
      centralPrefixMass ℓ f θ z H p.1 p.2) := by
  apply Measurable.ennreal_toReal
  apply measurable_from_prod_countable_left
  intro x
  exact (Kernel.measurable_coe _ (measurableSet_tubePrefix ℓ f x θ z H)).comp
    (measurable_id.prodMk measurable_const)
lemma jumpPrefixMass_measurable {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (b a s : ℝ) (H : ℕ) : Measurable (fun p : Environment d × Lattice d =>
      jumpPrefixMass ℓ f b a s H p.1 p.2) := by
  apply measurable_from_prod_countable_left
  intro x
  let E := EndpointPrefix ℓ x H {z | a < s*(signedCoordinate f (z-x)-b)}
  have hE : MeasurableSet E := measurableSet_endpointPrefix ℓ x H _
  have hh : Measurable (fun ω : Environment d => quenchedKernel (ω,x) E) :=
    (Kernel.measurable_coe quenchedKernel hE).comp (measurable_id.prodMk measurable_const)
  exact hh.ennreal_toReal

theorem clipped_pair_favorable_fraction {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e))) :
    ∃ a j c : ℝ, 0 < a ∧ 0 < j ∧ 0 < c ∧ ∀ δ : ℝ, 0 < δ →
      ∃ d₀ R : ℝ, 0 < d₀ ∧ 0 < R ∧ ∀ r : ℝ, R ≤ r →
        let H := ⌊fluctuationScale (independentConditionedPairLaw ν (realPosition (step e)))
          (commonIncrementProcess (realPosition (step e)) f 0) r⌋₊
        0 < H ∧ ∃ θ s : ℝ, (s=1 ∨ s= -1) ∧
        ∀ π : Measure (Lattice d × Lattice d), IsProbabilityMeasure π →
        c ≤ (environmentLaw ν).real {ω | c ≤ ∫ x,
          if j ≤ jumpPrefixMass (realPosition (step e)) f ((H:ℝ)*θ) (a*r) s H ω
              (if s=1 then x.2 else x.1) ∧
            d₀ ≤ centralPrefixMass (realPosition (step e)) f θ (δ*r) H ω x.1 ∧
            d₀ ≤ centralPrefixMass (realPosition (step e)) f θ (δ*r) H ω x.2
          then (1:ℝ) else 0 ∂π} := by
  let ℓ := realPosition (step e)
  let n := fun r => fluctuationScale (independentConditionedPairLaw ν ℓ) (commonIncrementProcess ℓ f 0) r
  obtain ⟨a,j,R,hapos,hjpos,hR,hjump⟩ := uniform_raw_jump ν hue e f hef htrans
  refine ⟨a,j,j/4,hapos,hjpos,by positivity,fun δ hδ => ?_⟩
  obtain ⟨d₀,hd₀,hd₁,R₁,hR₁,hclip⟩ := clipping_uniform ν hue e f hef htrans
    (by norm_num : 0 < (1:ℝ)) hδ (by positivity : 0 < j/4)
  have hdfin : d₀ ≠ ∞ := ne_top_of_le_ne_top (by simp) hd₁
  have hd : 0 < d₀.toReal := ENNReal.toReal_pos (ne_of_gt hd₀) hdfin
  refine ⟨d₀.toReal,max R R₁,hd,hR.trans_le (le_max_left _ _),fun r hr => ?_⟩
  obtain ⟨hH,hj⟩ := hjump r ((le_max_left R R₁).trans hr)
  obtain ⟨θ,hθ⟩ := hclip r ((le_max_right R R₁).trans hr)
  let H := ⌊n r⌋₊
  obtain ⟨s,hs,hjs⟩ := hj ((H:ℝ)*θ)
  refine ⟨hH,θ,s,hs,fun π hπ => ?_⟩
  let := hπ
  let A := fun (ω : Environment d) (x : Lattice d × Lattice d) =>
    j ≤ jumpPrefixMass ℓ f ((H:ℝ)*θ) (a*r) s H ω (if s=1 then x.2 else x.1) ∧
    d₀.toReal ≤ centralPrefixMass ℓ f θ (δ*r) H ω x.1 ∧
    d₀.toReal ≤ centralPrefixMass ℓ f θ (δ*r) H ω x.2
  have hm : MeasurableSet {p : Environment d × (Lattice d × Lattice d) | A p.1 p.2} := by
    have h₁ := (jumpPrefixMass_measurable ℓ f ((H:ℝ)*θ) (a*r) s H).comp
      (measurable_fst.prodMk ((measurable_of_countable (fun x : Lattice d × Lattice d => if s=1 then x.2 else x.1)).comp measurable_snd))
    have h₂ : Measurable (fun p : Environment d × (Lattice d × Lattice d) => centralPrefixMass ℓ f θ (δ*r) H p.1 p.2.1) := (centralPrefixMass_measurable ℓ f θ (δ*r) H).comp
      (measurable_fst.prodMk measurable_snd.fst)
    have h₃ : Measurable (fun p : Environment d × (Lattice d × Lattice d) => centralPrefixMass ℓ f θ (δ*r) H p.1 p.2.2) := (centralPrefixMass_measurable ℓ f θ (δ*r) H).comp
      (measurable_fst.prodMk measurable_snd.snd)
    exact (measurableSet_le measurable_const h₁).inter
      ((measurableSet_le measurable_const h₂).inter (measurableSet_le measurable_const h₃))
  have hb (x : Lattice d) : (environmentLaw ν).real
      {ω | ¬d₀.toReal ≤ centralPrefixMass ℓ f θ (δ*r) H ω x} ≤ j/4 := by
    have hnn : 0 ≤ n r := (Nat.floor_pos.mp hH).trans' (by norm_num)
    have hHn : (H:ℝ) ≤ 1*n r := by simpa [H] using Nat.floor_le hnn
    have hh := hθ x H hHn
    have he : {ω | ¬d₀.toReal ≤ centralPrefixMass ℓ f θ (δ*r) H ω x} =
        {ω | quenchedKernel (ω,x) (TubePrefix ℓ f x θ (δ*r) H) < d₀} := by
      ext ω
      simp only [not_le,centralPrefixMass,Measure.real]
      exact ENNReal.toReal_lt_toReal (measure_ne_top _ _) hdfin
    simpa only [he] using hh.le
  have hx (x : Lattice d × Lattice d) : j/2 ≤ (environmentLaw ν).real {ω | A ω x} := by
    have hh := favorable_pair_probability (environmentLaw ν)
      {ω | j ≤ jumpPrefixMass ℓ f ((H:ℝ)*θ) (a*r) s H ω (if s=1 then x.2 else x.1)}
      {ω | d₀.toReal ≤ centralPrefixMass ℓ f θ (δ*r) H ω x.1}
      {ω | d₀.toReal ≤ centralPrefixMass ℓ f θ (δ*r) H ω x.2}
      (measurableSet_le measurable_const ((jumpPrefixMass_measurable ℓ f _ _ _ _).comp
        (measurable_id.prodMk measurable_const)))
      (measurableSet_le measurable_const ((centralPrefixMass_measurable ℓ f _ _ _).comp
        (measurable_id.prodMk measurable_const)))
      (measurableSet_le measurable_const ((centralPrefixMass_measurable ℓ f _ _ _).comp
        (measurable_id.prodMk measurable_const)))
      (hjs (if s=1 then x.2 else x.1)) (hb x.1) (hb x.2)
    have he : j-2*(j/4)=j/2 := by ring
    have hsA : ({ω | j ≤ jumpPrefixMass ℓ f ((H:ℝ)*θ) (a*r) s H ω (if s=1 then x.2 else x.1)} ∩
      {ω | d₀.toReal ≤ centralPrefixMass ℓ f θ (δ*r) H ω x.1} ∩
      {ω | d₀.toReal ≤ centralPrefixMass ℓ f θ (δ*r) H ω x.2}) = {ω | A ω x} := by
      ext ω; simp only [Set.mem_inter_iff,Set.mem_ofPred_eq,A,and_assoc]
    simpa only [he,hsA] using hh
  have hh := favorable_fraction_probability (environmentLaw ν) π A hm (by positivity : 0 ≤ j/2) hx
  have he : (j/2)/2=j/4 := by ring
  rw [he] at hh
  convert hh using 1
  congr 1
  ext ω
  simp only [Set.mem_ofPred_eq]
  apply Iff.of_eq
  congr 1
  apply integral_congr_ae
  filter_upwards [] with x
  dsimp [A,H,n,ℓ]
  split_ifs <;> rfl
end DirectionalTransience

end

end

end OAI
