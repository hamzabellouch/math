import OAI.Probability.BenjaminiSchramm.CriticalEndpointProfiles
import OAI.Probability.BenjaminiSchramm.FullspaceFractionalRecurrence

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace Percolation.BenjaminiSchramm
variable {V E : Type*} [Encodable V] [Countable E] [Infinite V]
    (G : BondGraph V E) [Fintype (criticalModel G).VertexOrbit]

theorem critical_fullspace_threeQuarter_profiles
    (hc : Connected G) (hl : LocallyFinite G) (hq : QuasiTransitive G)
    (hpc1 : pc G < 1) (hu : ¬(criticalModel G).CombinatoriallyUnimodular)
    (μ : (criticalModel G).VertexOrbit → ℝ) (hμ : ∀ i, 0 < μ i)
    (hstat : orbitChainStep ((criticalModel G).orbitWalkKernel hl) μ=μ)
    (R : ℝ) (hR : 0 < R)
    (hjump : ∀ e v w, v ∈ G e → w ∈ G e →
      |(criticalModel G).orbitAdjustedHeight ((criticalModel G).stationaryOrbitWeight μ) v w| ≤ R) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧
      (∀ k : ℝ, 0 ≤ k → ∀ x : V,
      (∫⁻ ω, (restrictedLayerCount G Set.univ
        {v | k-R ≤ (criticalModel G).orbitAdjustedHeight ((criticalModel G).stationaryOrbitWeight μ) x v ∧
          (criticalModel G).orbitAdjustedHeight ((criticalModel G).stationaryOrbitWeight μ) x v ≤ k+R} ω x)^(3/4 : ℝ) ∂law (pc G)) ≤
        C*ENNReal.ofReal (Real.exp (-k/2))) ∧
      (∀ k : ℝ, 0 ≤ k → ∀ x : V,
      (∫⁻ ω, (restrictedLayerCount G Set.univ
        {v | -k-R ≤ (criticalModel G).orbitAdjustedHeight ((criticalModel G).stationaryOrbitWeight μ) x v ∧
          (criticalModel G).orbitAdjustedHeight ((criticalModel G).stationaryOrbitWeight μ) x v ≤ -k+R} ω x)^(3/4 : ℝ) ∂law (pc G)) ≤
        C*ENNReal.ofReal (Real.exp (k/16))) := by
  let H := criticalModel G
  let a := H.stationaryOrbitWeight μ
  let h := H.orbitAdjustedHeight a
  have hHc := criticalModel_connected G hc
  have hHq := criticalModel_quasiTransitive G hq
  have hp0 : (0 : ℝ) < pc G := by exact_mod_cast pc_pos G hl hq
  have hp1 : (pc G : ℝ) < 1 := by exact_mod_cast hpc1
  have hfin := critical_finite_general G hc hl hq hpc1
  obtain ⟨d,hd⟩ := exists_neighbor_card_bound G hl hq
  obtain ⟨hendup,henddown⟩ := critical_endpoint_fractional_profiles G hc hl hq hpc1 hu μ hμ hstat R hR hjump
  have hhalf := critical_halfspace_fractional_profiles G hc hl hq hpc1 hu μ hμ hstat R hR hjump
  have hbase (x z v : V) : h x v=h x z+h z v := H.orbitAdjustedHeight_change_base hHc hl a x z v
  have hself (x : V) : h x x=0 := H.orbitAdjustedHeight_self a x
  have hj (x : V) := H.height_difference_jump hHc hl a R hjump x
  obtain ⟨T₁,_hT₁,hshift₁⟩ := H.halfspace_ceiling_shift_profile_fixed hHc hl hHq μ hμ hstat hu R hR.le hjump
    (pc G) hp0 hp1 (1/4)
  obtain ⟨D₁,hD₁,hb₁⟩ := hshift₁ (7/8) (by norm_num) ((hhalf (7/8) (by norm_num) (by norm_num)).1 (1/4) (by norm_num))
  let D₁' := D₁*ENNReal.ofReal (Real.exp (T₁*R))
  have hD₁' : D₁' < ⊤ := ENNReal.mul_lt_top hD₁ ENNReal.ofReal_lt_top
  have hcont₁ (s : ℝ) (hs : 0 ≤ s) (z : V) :
      (∫⁻ ω, (restrictedLayerCount G (internalEdges G {v | h z v ≤ R})
        {v | -s-R ≤ h z v ∧ h z v ≤ -s+R} ω z)^(7/8 : ℝ) ∂law (pc G)) ≤
          D₁'*ENNReal.ofReal (Real.exp ((1/4)*s)) := by
    apply le_trans _ ((hb₁ s hs R hR.le z).trans_eq ?_)
    · rfl
    · dsimp [D₁']
      rw [Real.exp_add ((1/4)*s) (T₁*R),ENNReal.ofReal_mul (Real.exp_nonneg _)]
      ac_rfl
  have htop₁ : ∀ u ∈ ({(7/8 : ℝ),(7/8 : ℝ)*(7/8 : ℝ)} : Set ℝ), ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ k : ℝ, 0 ≤ k → ∀ x : V,
      (∫⁻ ω, (restrictedLayerCount G (internalEdges G {v | h x v ≤ k})
        {v | k-R ≤ h x v ∧ h x v ≤ k+R} ω x)^u ∂law (pc G)) ≤
          C*ENNReal.ofReal (Real.exp ((-1+ε)*k)) := by
    intro u hu ε hε
    have hu0 : 0 < u := by
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hu
      rcases hu with rfl | rfl <;> norm_num
    have hu1 : u < 1 := by
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hu
      rcases hu with rfl | rfl <;> norm_num
    exact hendup u hu0 hu1 ε hε
  obtain ⟨C₁,hC₁,hfull₁⟩ := fullspace_fractional_from_ceiling_profiles G hl d hd h hself hbase R hR
    hj (pc G) hfin (7/8) (7/8) (-1) (1/4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) htop₁ D₁' hD₁' hcont₁ (1/2) (by norm_num)
  obtain ⟨T₂,_hT₂,hshift₂⟩ := H.halfspace_floor_shift_profile_fixed hHc hl hHq μ hμ hstat hu R hR.le hjump
    (pc G) hp0 hp1 (-1+(1/2 : ℝ))
  obtain ⟨D₂,hD₂,hb₂⟩ := hshift₂ (7/8) (by norm_num) ((hhalf (7/8) (by norm_num) (by norm_num)).2 (1/2) (by norm_num))
  let D₂' := D₂*ENNReal.ofReal (Real.exp (T₂*R))
  have hD₂' : D₂' < ⊤ := ENNReal.mul_lt_top hD₂ ENNReal.ofReal_lt_top
  have hnegceil (x : V) (k : ℝ) : {v | -h x v ≤ k}={v | -k ≤ h x v} := by
    ext v
    change (-h x v ≤ k) ↔ -k ≤ h x v
    constructor <;> intro hv <;> linarith
  have hnegband (x : V) (k : ℝ) : {v | k-R ≤ -h x v ∧ -h x v ≤ k+R}=
      {v | -k-R ≤ h x v ∧ h x v ≤ -k+R} := by
    ext v
    constructor <;> intro hv <;> constructor <;> linarith [hv.1,hv.2]
  have hnegcont (x : V) (k : ℝ) : {v | -k-R ≤ -h x v ∧ -h x v ≤ -k+R}=
      {v | k-R ≤ h x v ∧ h x v ≤ k+R} := by
    ext v
    constructor <;> intro hv <;> constructor <;> linarith [hv.1,hv.2]
  have hcont₂ (s : ℝ) (hs : 0 ≤ s) (z : V) :
      (∫⁻ ω, (restrictedLayerCount G (internalEdges G {v | -h z v ≤ R})
        {v | -s-R ≤ -h z v ∧ -h z v ≤ -s+R} ω z)^(7/8 : ℝ) ∂law (pc G)) ≤
          D₂'*ENNReal.ofReal (Real.exp ((-1/2)*s)) := by
    rw [hnegceil,hnegcont]
    apply le_trans _ ((hb₂ s hs R hR.le z).trans_eq ?_)
    · rfl
    · dsimp [D₂']
      rw [Real.exp_add ((-1+(1/2 : ℝ))*s) (T₂*R),ENNReal.ofReal_mul (Real.exp_nonneg _)]
      rw [show (-1+(1/2 : ℝ))*s=(-1/2)*s by ring]
      ac_rfl
  have htop₂ : ∀ u ∈ ({(7/8 : ℝ),(7/8 : ℝ)*(7/8 : ℝ)} : Set ℝ), ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ k : ℝ, 0 ≤ k → ∀ x : V,
      (∫⁻ ω, (restrictedLayerCount G (internalEdges G {v | -h x v ≤ k})
        {v | k-R ≤ -h x v ∧ -h x v ≤ k+R} ω x)^u ∂law (pc G)) ≤
          C*ENNReal.ofReal (Real.exp ((0+ε)*k)) := by
    intro u hu ε hε
    have hu0 : 0 < u := by
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hu
      rcases hu with rfl | rfl <;> norm_num
    have hu1 : u < 1 := by
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hu
      rcases hu with rfl | rfl <;> norm_num
    obtain ⟨C,hC,hb⟩ := henddown u hu0 hu1 ε hε
    refine ⟨C,hC,fun k hk x => ?_⟩
    simpa only [hnegceil,hnegband,zero_add] using hb k hk x
  obtain ⟨C₂,hC₂,hfull₂⟩ := fullspace_fractional_from_ceiling_profiles G hl d hd
    (fun x v => -h x v) (fun x => by simp only [hself,neg_zero])
    (fun x z v => by rw [hbase]; ring) R hR
    (fun x e u v hu hv => by simpa only [neg_sub_neg,abs_sub_comm] using hj x e u v hu hv)
    (pc G) hfin (7/8) (7/8) 0 (-1/2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) htop₂ D₂' hD₂' hcont₂ (1/16) (by norm_num)
  have hmono (W : Set V) (x : V) :
      (∫⁻ ω, (restrictedLayerCount G Set.univ W ω x)^(3/4 : ℝ) ∂law (pc G)) ≤
      (∫⁻ ω, (restrictedLayerCount G Set.univ W ω x)^((7/8 : ℝ)*(7/8 : ℝ)) ∂law (pc G)) := by
    apply lintegral_mono
    intro ω
    rcases restrictedLayerCount_zero_or_one_le G Set.univ W ω x with hz | ho
    · simp only [hz,ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 3/4),
        ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < (7/8)*(7/8)),le_refl]
    · exact ENNReal.rpow_le_rpow_of_exponent_le ho (by norm_num)
  refine ⟨C₁+C₂,ENNReal.add_lt_top.mpr ⟨hC₁,hC₂⟩,?_,?_⟩
  · intro k hk x
    apply (hmono _ x).trans ((hfull₁ k hk x).trans ?_)
    have he : (-1+(1/2 : ℝ))*k= -k/2 := by ring
    rw [he]
    exact mul_le_mul' le_self_add le_rfl
  · intro k hk x
    have hh := hfull₂ k hk x
    simp only [hnegband,zero_add] at hh
    apply (hmono _ x).trans (hh.trans ?_)
    have he : (1/16 : ℝ)*k=k/16 := by ring
    rw [he]
    exact mul_le_mul' le_add_self le_rfl

end Percolation.BenjaminiSchramm

end

end OAI
