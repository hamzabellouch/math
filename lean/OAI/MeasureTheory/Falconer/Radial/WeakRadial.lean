import OAI.MeasureTheory.Falconer.Radial.SingleScaleWeakRadial
import OAI.MeasureTheory.Falconer.Radial.RadialAllRadiusBound
import OAI.MeasureTheory.Falconer.Radial.RadialRemoveDiagonal

namespace OAI

/-! # The weak radial estimate in every dimension, at finite dyadic scales

This is Lemma `ang:weak-radial` of the manuscript, with the bounded support
specified by a unit dyadic cube. The only published input here is the finite
coordinate form of Loomis--Whitney. All pair deletions use the original law.
-/

namespace Falconer
open Set Metric MeasureTheory NormedSpace
open scoped ENNReal
variable {n : ℕ}

theorem weak_radial (hLW : PublishedFiniteLoomisWhitney) (hn : 1 ≤ n)
    {ζ ell e : ℝ} (hζ : 0 < ζ) (hell0 : 0 ≤ ell)
    (hell : ell < ((n:ℝ)/(n+1))*(n:ℝ)) (he : 0 < e)
    (Q : DyadicCube (n+1)) (hQ : Q.side = 1) {M : ℝ} (hM : 1 ≤ M)
    (hbounded : ∀ x ∈ Q.carrier, ‖x‖ ≤ M) :
    ∃ ε c : ℝ, 0 < ε ∧ 0 < c ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ (μ : Measure (Space (n+1))) [IsProbabilityMeasure μ], μ Q.carrierᶜ = 0 →
      (∀ x : Space (n+1), ∀ r : ℝ, ((2:ℝ)^N)⁻¹ ≤ r → r ≤ 1 →
        μ (ball x r) ≤ ENNReal.ofReal (((2:ℝ)^N)^ε*r^(n:ℝ))) →
      (∀ w : Space (n+1), ‖w‖ = 1 → ∀ a r : ℝ, ((2:ℝ)^N)⁻¹ ≤ r → r ≤ 1 →
        μ {x | |inner ℝ w x-a| ≤ r} ≤ ENNReal.ofReal (((2:ℝ)^N)^ε*r^ζ)) →
      ∃ G : Set (Space (n+1) × Space (n+1)), MeasurableSet G ∧
        (∀ x : Space (n+1), (x,x) ∉ G) ∧
        (μ.prod μ) Gᶜ ≤ ENNReal.ofReal (((2:ℝ)^N)^(-c)) ∧
        ∀ x w : Space (n+1), ∀ r : ℝ, ((2:ℝ)^N)⁻¹ ≤ r → r ≤ 1 →
          μ {z | (x,z) ∈ G ∧ ‖normalize (z-x)-w‖ ≤ r} ≤
            ENNReal.ofReal (((2:ℝ)^N)^e*r^ell) := by
  classical
  obtain ⟨ell₁,hell₁,hupper⟩ := exists_between hell
  have hell₁0 : 0 < ell₁ := lt_of_le_of_lt hell0 hell₁
  obtain ⟨eps,cs,heps,hcs,Ns,hs⟩ := single_scale_weak_radial hLW hn hζ hupper Q hQ hM hbounded
  obtain ⟨K₀,hK₀⟩ := exists_nat_gt (ell/e)
  let K := K₀+1
  have hK : 0 < K := by dsimp [K]; omega
  have hKr : (0:ℝ) < K := by exact_mod_cast hK
  have hKell : ell ≤ e*(K:ℝ) := by
    have hh := (div_lt_iff₀ he).mp hK₀
    dsimp [K]
    push_cast
    nlinarith
  obtain ⟨cw,hcw,Nw,hw⟩ := radial_scale_window_cost K hK hcs
  let c := min cw ell₁/2
  have hc : 0 < c := half_pos (lt_min hcw hell₁0)
  have hccw : c < cw := by dsimp [c]; have := min_le_left cw ell₁; linarith
  have hcell : c < ell₁ := by dsimp [c]; have := min_le_right cw ell₁; linarith
  obtain ⟨Nc,hcost⟩ := weak_radial_two_costs (A := 1) (B := 1)
    (by norm_num) (by norm_num) hccw hcell
  obtain ⟨Nf,hfixed⟩ := Regularization.fixed_constant_absorbed he ((2:ℝ)^ell₁)
  refine ⟨eps/(2*(K:ℝ)),c,by positivity,hc,2*K+K*Ns+Nw+Nc+Nf,?_⟩
  intro N hN μ _ hroot hball hslab
  have hNhalf : 2*K ≤ N := by omega
  have hNs : Ns ≤ N/K := (Nat.le_div_iff_mul_le hK).mpr (by nlinarith)
  let I := Finset.Icc (N/K) N
  have hex : ∀ j : ℕ, ∃ G : Set (Space (n+1) × Space (n+1)), j ∈ I →
      MeasurableSet G ∧ (μ.prod μ) Gᶜ ≤ ENNReal.ofReal (((2:ℝ)^j)^(-cs)) ∧
      ∀ x w : Space (n+1), μ {z | (x,z) ∈ G ∧ ‖normalize (z-x)-w‖ ≤ ((2:ℝ)^j)⁻¹} ≤
        ENNReal.ofReal (((2:ℝ)^j)^(-ell₁)) := by
    intro j
    by_cases hj : j ∈ I
    · obtain ⟨hjB,hjN⟩ := Finset.mem_Icc.mp hj
      have hloss := radial_scale_window_loss hK hNhalf hjB heps.le
      have hradii : ((2:ℝ)^N)⁻¹ ≤ ((2:ℝ)^j)⁻¹ :=
        inv_anti₀ (by positivity) (pow_le_pow_right₀ (by norm_num) hjN)
      obtain ⟨G,hG,hcostG,hcapG⟩ := hs j (hNs.trans hjB) μ hroot
        (fun x r hr hr1 => (hball x r (hradii.trans hr) hr1).trans
          (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hloss (Real.rpow_nonneg (le_trans (by positivity) hr) _))))
        (fun w hw a r hr hr1 => (hslab w hw a r (hradii.trans hr) hr1).trans
          (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hloss (Real.rpow_nonneg (le_trans (by positivity) hr) _))))
      exact ⟨G,fun _ => ⟨hG,hcostG,hcapG⟩⟩
    · exact ⟨∅,fun h => (hj h).elim⟩
  choose G hG using hex
  obtain ⟨H,hH,hcostH,hcapH⟩ := finite_radial_scale_intersection μ μ I G
    (fun j => ENNReal.ofReal (((2:ℝ)^j)^(-cs)))
    (fun j => ENNReal.ofReal (((2:ℝ)^j)^(-ell₁))) (fun j => ((2:ℝ)^j)⁻¹)
    (fun j hj => (hG j hj).1) (fun j hj => (hG j hj).2.1) (fun j hj => (hG j hj).2.2)
  have hNI : N ∈ I := Finset.mem_Icc.mpr ⟨Nat.div_le_self N K,le_rfl⟩
  obtain ⟨H',hH',hsub,hdiag,hcostH'⟩ := radial_remove_diagonal μ H hH (by positivity)
    (ENNReal.ofReal (((2:ℝ)^N)^(-ell₁))) (hcapH N hNI _ le_rfl)
  refine ⟨H',hH',hdiag,hcostH'.trans ?_,?_⟩
  · apply (add_le_add (hcostH.trans (hw N (by omega))) le_rfl).trans
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    exact ENNReal.ofReal_le_ofReal (by simpa only [one_mul] using hcost N (by omega))
  · have hcap' := radial_all_radius_bound μ H N K hell0 hell₁.le he.le hKell
      (hfixed N (by omega)) (fun j hj => hcapH j hj _ le_rfl)
    intro x w r hr hr1
    apply (measure_mono ?_).trans (hcap' x w r hr hr1)
    exact fun z hz => ⟨hsub hz.1,hz.2⟩

end Falconer

end OAI
