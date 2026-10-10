import OAI.MeasureTheory.Falconer.Radial.EndpointSourceMiddle
import OAI.MeasureTheory.Falconer.Radial.SourceClassOuterRadial
import OAI.MeasureTheory.Falconer.Recursion.SourceClassIntervals
import OAI.MeasureTheory.Falconer.Estimates.RelativePairCore
import OAI.MeasureTheory.Falconer.Angular.ReverseCapsAllRadii
import OAI.MeasureTheory.Falconer.Geometry.UniformMiddleGeometry
import OAI.MeasureTheory.Falconer.Recursion.ThreeIntervalDyadicGain
import OAI.MeasureTheory.Falconer.Recursion.ThreeIntervalCost
import OAI.MeasureTheory.Falconer.Recursion.ThreeIntervalShift
import OAI.MeasureTheory.Falconer.Geometry.OneScaleGeometry

namespace OAI

/-! # Endpoint one-scale gain for an actual source class with a contact interval

All three local estimates are applied to the original conditional source laws.
The incoming relation and pin law are never renormalized.
-/

namespace Falconer.Regularization
open Set MeasureTheory NormedSpace
open scoped ENNReal BigOperators
attribute [local instance] Classical.propDecidable

theorem endpoint_contact_gain (hLW : PublishedFiniteLoomisWhitney)
    {h : ℕ} {t q ζ : ℝ} (hq : q = (h:ℝ)+1)
    (ht : (h:ℝ)+3/2 < t) (ht' : t < (h:ℝ)+2) (hζ : 0 < ζ)
    (Q : DyadicCube (h+3)) (hQ : Q.side = 1)
    {D s : ℝ} (hD : 1 ≤ D) (hDdim : Real.sqrt (h+3:ℕ) ≤ D) (hs : 0 < s) :
    ∃ ε gain : ℝ, 0 < ε ∧ 0 < gain ∧
      ∀ τ γ : ℝ, 0 < τ → 0 < γ →
        (2*((h+3:ℕ):ℝ)+4)*τ ≤ ε/2 →
        (20*(2*((h+3:ℕ):ℝ)+4)+4)*τ ≤ gain/8 → 2*τ ≤ gain →
      ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ (μ ν : Measure (Space (h+3))) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν],
      ∀ B : ℕ, 0 < B → ∀ lam : ℝ, 0 ≤ lam → lam ≤ τ*γ →
        (B:ℝ) ≤ lam*(N:ℝ) → (2:ℝ)^(N/B+2) ≤ ((2:ℝ)^N)^lam →
      ∀ p₀ ∈ regularizationLeaves Q μ N,
        RobustProfileContact (sourceUnitProfile Q μ N B p₀) q t τ γ →
      ∀ A P : Set (Space (h+3)), MeasurableSet A → MeasurableSet P →
        μ Aᶜ = 0 → ν Pᶜ = 0 →
        (∀ z ∈ A, ∀ x ∈ P, s ≤ ‖z-x‖) →
        (∀ y ∈ Q.carrier, ∀ x ∈ P, ‖y-x‖ ≤ D) →
      ∀ G : Set (Space (h+3) × Space (h+3)), MeasurableSet G →
        (∀ᵐ z ∂μ, ∀ r : ℝ, 1/(2:ℝ)^N ≤ r → r ≤ 1 →
          ∀ u : Space (h+3), ‖u‖ = 1 →
            ν {x | (z,x) ∈ G ∧ dist (normalize (x-z)) u < r} ≤
              ENNReal.ofReal (((2:ℝ)^N)^(τ*γ)*r^q)) →
        (∀ᵐ z ∂μ, ∀ u : Space (h+3), ‖u‖ = 1 → ∀ r : ℝ,
          1/(2:ℝ)^N ≤ r → r ≤ 1 →
            ν {x | (z,x) ∈ G ∧ |inner ℝ u (normalize (x-z))| ≤ r} ≤
              ENNReal.ofReal (((2:ℝ)^N)^(τ*γ)*r^ζ)) →
      ∃ G' : Set (Space (h+3) × Space (h+3)), MeasurableSet G' ∧ G' ⊆ G ∧
        ((sourceClass Q μ N B p₀).prod ν) (G \ G') ≤
          ENNReal.ofReal (((2:ℝ)^N)^(-(τ*γ/2))) ∧
        ∀ x u : Space (h+3), sourceClass Q μ N B p₀
          {z | (z,x) ∈ G' ∧ ‖normalize (z-x)-u‖ ≤ 1/(2:ℝ)^N} ≤
            ENNReal.ofReal (((2:ℝ)^N)^(-q-gain*γ/8)) := by
  obtain ⟨ε,gain,hε,hgain,M₀,hmiddle⟩ :=
    endpoint_source_class_middle_pruning hLW ht ht' hζ
  refine ⟨ε,gain,hε,hgain,?_⟩
  intro τ γ hτ hγ hτε hτgain hτgain'
  let L : ℝ := 2*((h+3:ℕ):ℝ)+4
  let σ : ℝ := cellContraction (h+3)
  let C : ℝ := 4*Real.sqrt (h+3:ℕ)/s+2
  have hL : 1 ≤ L := by dsimp [L]; have hh := Nat.cast_nonneg (α := ℝ) (h+3); linarith only [hh]
  have hq0 : 0 ≤ q := by rw [hq]; positivity
  have ht0 : 0 ≤ t := by have hh := Nat.cast_nonneg (α := ℝ) h; linarith only [hh,ht]
  have hside : 0 < Q.side := by rw [hQ]; norm_num
  have hσ : 0 < σ := cellContraction_pos _
  have hη₀ : 0 < L*τ*γ := by positivity
  obtain ⟨Jo,No,houter⟩ := source_class_outer_radial_pruning Q hQ hD hDdim hη₀ hq0 C
  obtain ⟨Jm,Nm,hgeom⟩ := uniform_middle_geometry hσ (by positivity : 0 < s/2)
    (by positivity : 0 < γ/2) D C M₀
  obtain ⟨Na,hmargin⟩ := eventually_integer_margin (by positivity : 0 < γ/2) Jo
  obtain ⟨Ns,hsmall⟩ := eventually_cell_diameter_small (h+3) (by positivity : 0 < γ/2) hs
  let K : ℝ := (((2*Nat.ceil (2+4*Real.sqrt (h+3:ℕ))+1)^(h+3):ℕ):ℝ)
  obtain ⟨Nf,hfirst⟩ := eventually_contact_outer_coefficient (h+3) hτ hγ (K*(2:ℝ)^q) 0
  obtain ⟨Nl,hlast⟩ := eventually_contact_outer_coefficient (h+3) hτ hγ
    (K*(2:ℝ)^q) (((h+3:ℕ):ℝ)+q)
  obtain ⟨Nt,htcoef⟩ := eventually_contact_frostman_coefficient (h+3) hτ hγ hτε
    (K*(2:ℝ)^t*σ^(-t)) (((h+3:ℕ):ℝ)+t)
  obtain ⟨Nc,hconst⟩ := fixed_constant_absorbed (mul_pos hτ hγ)
    (((2:ℝ)^Jm)^(q+gain/2))
  obtain ⟨Nd,hcost⟩ := eventually_three_interval_cost hτ hγ
    (by linarith : 1 ≤ 2*L) hτgain'
  obtain ⟨Nlarge,hlarge⟩ := exists_nat_gt (4/γ)
  let N₀ := max 1 (max No (max Nm (max Na (max Ns (max Nf (max Nl (max Nt
    (max Nc (max Nd Nlarge)))))))))
  refine ⟨N₀,?_⟩
  intro N hN μ ν _ _ B hB lam hlam hlamτ hblock hblock'
    p₀ hp₀ hcontact A P hA hP hAfull hPfull hsep hpin G hG hcap hslab
  change max 1 (max No (max Nm (max Na (max Ns (max Nf (max Nl (max Nt
    (max Nc (max Nd Nlarge))))))))) ≤ N at hN
  simp only [max_le_iff] at hN
  rcases hN with ⟨h1,hNo,hNm,hNa,hNs,hNf,hNl,hNt,hNc,hNd,hNL⟩
  have hNp : 0 < N := by omega
  have hNN : (Nlarge:ℝ) ≤ N := by exact_mod_cast hNL
  have hlarge' : 4 ≤ γ*(N:ℝ) := by
    have hh := (div_lt_iff₀ hγ).mp hlarge
    nlinarith only [hh,hNN,hγ]
  obtain ⟨α,β,a,b,hγΔ,hΔ1,hab,hbN,hgap,_,ha,_,hNb,hfreeze,hi₀,hi₁,hi₂⟩ :=
    source_class_contact_intervals Q μ hNp hB p₀ hq0 ht0 hγ hlarge' hcontact
  let Δ := β-α
  let η := L*τ*Δ
  let ξ := τ*Δ
  let M := (b-a)-Jm
  have hΔ : 0 < Δ := hγ.trans_le hγΔ
  have hη : L*τ*γ ≤ η := mul_le_mul_of_nonneg_left hγΔ (by positivity)
  obtain ⟨hJm,hM,hNM,hfr,hwi⟩ := hgeom N hNm a b Δ hab
    (by dsimp [Δ]; linarith only [hγΔ,hγ]) hgap hfreeze
  have hJoA : Jo ≤ a := hmargin N hNa a ha
  have hJoB : b+Jo ≤ N := by
    have hh := hmargin N hNa (N-b) (by linarith only [hNb,hγ])
    omega
  have hsmallA : Real.sqrt (h+3:ℕ)*(Q.side/(2:ℝ)^a) ≤ s/2 := by
    rw [hQ,mul_one_div]
    exact hsmall N hNs a ha
  have hsmallAll {n : ℕ} (han : a ≤ n) :
      Real.sqrt (h+3:ℕ)*(Q.side/(2:ℝ)^n) ≤ s/2 := by
    apply le_trans _ hsmallA
    exact mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_left hside.le (by positivity)
        (pow_le_pow_right₀ (by norm_num) han)) (Real.sqrt_nonneg _)
  have hcoef₀ : K*(2:ℝ)^q*((2:ℝ)^N)^(τ*Δ+2*(((h+3:ℕ):ℝ)+1)*lam) ≤
      ((2:ℝ)^N)^η := by
    simpa only [zero_div,add_zero] using hfirst N hNf hNp Δ lam hγΔ hlamτ
  have hcoef₂ := hlast N hNl hNp Δ lam hγΔ hlamτ
  have hcoef₁ : K*(2:ℝ)^t*((2:ℝ)^N)^
      ((τ*Δ+(((h+3:ℕ):ℝ)+t)/(N:ℝ))+2*(((h+3:ℕ):ℝ)+1)*lam)*σ^(-t) ≤
      (1/(2:ℝ)^M)^(-ε) := by
    convert htcoef N hNt hNp M Δ lam hγΔ hlamτ hNM using 1; ring
  have hreverseOuter : ((2:ℝ)^N)^(τ*γ) ≤ ((2:ℝ)^N)^η := by
    apply Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num))
    have hh := mul_le_mul_of_nonneg_right hL (mul_nonneg hτ.le hγ.le)
    dsimp [η]
    nlinarith only [hh,hη]
  have hreverseMiddle : ((2:ℝ)^N)^(τ*γ) ≤ (1/(2:ℝ)^M)^(-ε) := by
    rw [inverse_dyadic_neg_power]
    apply dyadic_relative_scale_bound
    have hh := contact_loss_relative_budget hτ.le hγΔ hlamτ hτε hNM
    have hx : 0 ≤ (N:ℝ)*(τ*Δ+2*(((h+3:ℕ):ℝ)+1)*lam) := by positivity
    nlinarith only [hh,hx]
  let ρ := sourceClass Q μ N B p₀
  have : IsProbabilityMeasure ρ := regularization_class_probability Q hside μ N B hp₀
  have hρA : ρ Aᶜ = 0 := sourceClass_absolutelyContinuous Q μ N B p₀ hAfull
  obtain ⟨G₀,hG₀,hG₀G,hG₀core,hnull⟩ :=
    source_class_pair_core Q hside μ ν N B p₀ hp₀ A P hA hP hAfull hPfull G hG
  have hcore : G₀ ⊆ Q.occupiedTreeCore ρ N ×ˢ P := fun _ hz => ⟨(hG₀core hz).1.2,(hG₀core hz).2⟩
  have hdiag {z x : Space (h+3)} (hz : (z,x) ∈ G₀) : z ≠ x := by
    have hh := hsep z (hG₀core hz).1.1 x (hG₀core hz).2
    intro he
    simp only [he,sub_self,norm_zero] at hh
    exact (not_le_of_gt hs) hh
  let cost : ℕ → ℝ≥0∞ := fun j => if j = 1 then 2*ENNReal.ofReal ((1/(2:ℝ)^M)^gain)
    else ENNReal.ofReal (((2:ℝ)^N)^(-(2*η)))
  have hlocal : ∀ j < 3, ∀ p ∈ Q.occupiedPaths ρ (threeIntervalDepth a b N j),
      ∃ H : Set (Space (h+3) × Space (h+3)), MeasurableSet H ∧
      ((ProbabilityTheory.cond ρ (Q.descendant p).carrier).prod ν)
        ((G₀ ∩ ((Q.descendant p).carrier ×ˢ univ)) \ H) ≤ cost j ∧
      ∀ z ∈ H, radialCollisionMass (ProbabilityTheory.cond ρ (Q.descendant p).carrier)
        (C/(2:ℝ)^(threeIntervalDepth a b N (j+1))) z ≤
          threeIntervalFactor a b N Jm q (gain/2) η j := by
    intro j hj p hp
    have hpPos : 0 < ρ (Q.descendant p).carrier := (Finset.mem_filter.mp hp).2
    have hpLen : p.length = threeIntervalDepth a b N j :=
      (mem_cubePaths _ _ _).mp (Finset.mem_filter.mp hp).1
    let V := G₀ ∩ ((Q.descendant p).carrier ×ˢ univ)
    have hV : MeasurableSet V := hG₀.inter ((Q.descendant p).measurable.prod MeasurableSet.univ)
    have hVG : V ⊆ G := inter_subset_left.trans hG₀G
    have hVdiag : ∀ z x, (z,x) ∈ V → x ≠ z := fun _ _ hz => (hdiag hz.1).symm
    have hVpin : ∀ z x, (z,x) ∈ V → ∀ y ∈ (Q.descendant p).carrier, ‖y-x‖ ≤ D :=
      fun _ _ hz y hy => hpin y (Q.descendant_subset p hy) _ (hG₀core hz.1).2
    have hac := sourceClass_conditional_absolutelyContinuous Q μ N B p₀ p
    interval_cases j
    · have hlen : p.length = 0 := by simpa [threeIntervalDepth] using hpLen
      obtain ⟨H,hH,_,hd,hk⟩ := houter N hNo η hη 0 a (by omega) (hab.trans hbN)
        μ ν B hNp hB lam (τ*Δ) hblock hblock' p₀ hp₀ p hlen hpPos
        (by intro n _ hn; simpa only [Nat.sub_zero,sourceProfile,Nat.cast_zero,regularizedProfile_zero,sub_zero] using hi₀ n hn)
        hcoef₀ V hV hVdiag hVpin
        (reverse_caps_all_radii μ _ ν hac hVG (hab.trans hbN) hreverseOuter hcap)
      refine ⟨H,hH,?_,?_⟩
      · simpa [cost] using hd
      · simpa [threeIntervalDepth,threeIntervalFactor] using hk
    · have hlen : p.length = a := by simpa [threeIntervalDepth] using hpLen
      have hp' : p ∈ Q.occupiedPaths ρ a := by simpa [threeIntervalDepth] using hp
      let w₀ : Sphere (h+3) := ⟨EuclideanSpace.basisFun (Fin (h+3)) ℝ 0,by
        simpa only [Metric.mem_sphere,dist_zero_right] using
          (EuclideanSpace.basisFun (Fin (h+3)) ℝ).norm_eq_one 0⟩
      obtain ⟨H,hH,_,hd,hk⟩ := hmiddle M hM Q hQ μ ν (by simp) N B hNp hB lam
        (τ*Δ+(((h+3:ℕ):ℝ)+t)/(N:ℝ)) σ (by positivity) hlam hσ
        (cellContraction_le_one _) (cellContraction_sqrt _) hblock hblock' p₀ hp₀
        a b hab hbN (Nat.sub_le _ _) p hlen hpPos
        (by intro n hn hn'; have hh := hi₁ n hn hn'; linarith only [hh]) hcoef₁ w₀ V hV
        (fun z x hz => ⟨hdiag hz.1,hz.2.1⟩)
        (by
          have hmN : M ≤ N := (Nat.sub_le _ _).trans ((Nat.sub_le _ _).trans hbN)
          have hcm := reverse_caps_transfer μ _ ν hac hVG hmN hreverseMiddle hcap
          have hsm := reverse_slabs_transfer μ _ ν hac hVG hmN hreverseMiddle hslab
          filter_upwards [hcm,hsm] with z hz hs'
          exact ⟨by simpa only [hq] using hz,hs'⟩)
        (s/2) D (C/(2:ℝ)^b) (by positivity) hfr hwi (by
          intro x hx
          obtain ⟨z,hz⟩ := hx
          refine ⟨occupied_cell_center_separation Q hside ρ A P hρA hsep hsmallA hp'
            x (hG₀core hz.1).2,?_⟩
          exact ProbabilityTheory.ae_cond_of_forall_mem (Q.descendant p).measurable
            (fun y hy => hVpin z x hz y hy))
      refine ⟨H,hH,?_,?_⟩
      · simpa [cost] using hd
      · simpa [threeIntervalDepth,threeIntervalFactor,M,hq] using hk
    · have hlen : p.length = b := by simpa [threeIntervalDepth] using hpLen
      obtain ⟨H,hH,_,hd,hk⟩ := houter N hNo η hη b N hJoB le_rfl
        μ ν B hNp hB lam (τ*Δ+(((h+3:ℕ):ℝ)+q)/(N:ℝ)) hblock hblock' p₀ hp₀ p hlen hpPos
        (by intro n hn hn'; have hh := hi₂ n hn hn'; linarith only [hh])
        hcoef₂ V hV hVdiag hVpin (reverse_caps_all_radii μ _ ν hac hVG le_rfl hreverseOuter hcap)
      refine ⟨H,hH,?_,?_⟩
      · simpa [cost] using hd
      · simpa [threeIntervalDepth,threeIntervalFactor] using hk
  have hβ : (Δ/2)*(N:ℝ) ≤ (b-a:ℕ) := by
    have hh : ((b-a)-Jm:ℕ) ≤ b-a := Nat.sub_le _ _
    have hh' : (M:ℝ) ≤ (b-a:ℕ) := by exact_mod_cast hh
    nlinarith only [hh',hNM]
  have hconst' : ((2:ℝ)^Jm)^(q+gain/2) ≤ ((2:ℝ)^N)^ξ :=
    (hconst N hNc).trans (Real.rpow_le_rpow_of_exponent_le
      (one_le_pow₀ (by norm_num)) (mul_le_mul_of_nonneg_left hγΔ hτ.le))
  have hbudget : 20*η+4*ξ+gain*γ/8 ≤ (gain/2)*(Δ/2) :=
    three_interval_relative_budget hΔ.le hγΔ hgain.le hτgain
  obtain ⟨G',hG',hsub,hdel,hcaps⟩ := three_interval_dyadic_gain ρ ν Q hside hab hbN hJm
    A P hρA hs hsep G₀ hG₀ hcore
    (fun j => C/(2:ℝ)^(threeIntervalDepth a b N (j+1))) cost
    (by positivity : 0 ≤ gain/2) hβ hconst' hbudget
    (fun j hj => hsmallAll (threeIntervalDepth_child hab hbN hj))
    (fun j hj => by
      rw [hQ]
      exact dyadic_collision_width (h+3) hs le_rfl
        (threeIntervalDepth_le hab hbN (by omega))) hlocal
  refine ⟨G',hG',hsub.trans hG₀G,?_,hcaps⟩
  have hz : (ρ.prod ν) (G \ G₀) ≤ 0 := hnull.le
  have htotal := relative_pruning_cost_trans (ρ.prod ν) G G₀ G' hz hdel
  rw [zero_add] at htotal
  apply htotal.trans
  have hc := hcost N hNd M Δ hγΔ hNM
  have he : (∑ j ∈ Finset.range 3, cost j)+4*ENNReal.ofReal (((2:ℝ)^N)^(-ξ)) =
      ENNReal.ofReal (2*((2:ℝ)^N)^(-(2*η))+2*(1/(2:ℝ)^M)^gain+
        4*((2:ℝ)^N)^(-ξ)) := by
    rw [ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_add (by positivity) (by positivity)]
    simp only [Finset.sum_range_succ,Finset.sum_range_zero,cost,show (0:ℕ) ≠ 1 by omega,
      show (2:ℕ) ≠ 1 by omega,ite_false,ite_true,zero_add,
      ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2),
      ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 4),ENNReal.ofReal_ofNat]
    ring
  rw [he]
  exact ENNReal.ofReal_le_ofReal hc

end Falconer.Regularization

end OAI
