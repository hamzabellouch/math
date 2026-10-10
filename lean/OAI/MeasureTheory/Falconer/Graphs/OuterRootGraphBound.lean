import OAI.MeasureTheory.Falconer.Estimates.OuterChildProfileBound
import OAI.MeasureTheory.Falconer.Estimates.OuterRootEquation21
import OAI.MeasureTheory.Falconer.Estimates.ActualDistanceEquation12

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff ENNReal

theorem uniform_outer_root_graph_bound {lam sig kap eta T : ℝ}
    (hlam : 0 ≤ lam) (hsig : 0 < sig) (hkap : 0 < kap) (hkap1 : kap ≤ 1)
    (hgap : sig < kap/1000) (hloss : 4000*(lam+sig) ≤ 1)
    (heta : 0 < eta) (hT : 0 ≤ T) (n : ℕ)
    {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) (hpos : ∀ x, 0 ≤ Ψ x)
    (hs : ∀ x, Ψ x ≠ 0 → x ∈ Ioo (1/4:ℝ) 4)
    (hone : ∀ x ∈ Icc (1/2:ℝ) 2, 1 ≤ Ψ x) :
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ N ≥ N₀,
      ∀ (Q : Fin 2 → DyadicSquare) (ρ : Fin 2 → Measure Plane) (mass : Fin 2 → ℝ → ℝ),
      (∀ l, (Q l).side = 1) → (∀ l, ρ l (Q l).carrierᶜ = 0) →
      100 ≤ dist (Q 0).center (Q 1).center → dist (Q 0).center (Q 1).center ≤ 2000 →
      ∀ B : ℕ, ∀ δ : ℝ, (∀ l, RegularizedProfileData (Q l) (ρ l) N B δ lam (mass l)) →
      ∀ c : ℕ, c+100*sourcePolicyBlock N kap < N → kap*N ≤ (c:ℝ) → 2*c ≤ N →
      let A := fun l (t : ℕ) => mass l t-(t:ℝ)/N
      let d := RootShellData.ofOuter (Q 0) (Q 1) (ρ 0) (ρ 1) (mass 0) (mass 1)
        N lam lam sig kap c (Q 0) (Q 1)
      let bound := ((2:ℝ)^N)^(min (height (A 0) 0 c) (height (A 1) 0 c)-
        (potential (A 0) c N (10*sourcePolicyBlock N kap)+
         potential (A 1) c N (10*sourcePolicyBlock N kap))/2+
        500*kap+10^6*(lam+sig)/kap+4000*(lam+sig)+eta)+((2:ℝ)^N)^(-T)
      (∀ j ∈ Finset.range (n+1), ∀ b ∈ inverseLeibnizTerms j d.indices, ∀ ξ,
        d.inversePhasedHF N Ψ b.2 ξ ≠ ⊤ ∧ (d.inversePhasedHF N Ψ b.2 ξ).toReal ≤ bound) ∧
      d.inverseShellSupremum n N Ψ ≤ bound := by
  classical
  have hJ := sourceSmoothingLevels_pos hsig hkap
  obtain ⟨N₁,hN₁,h₁⟩ := uniform_outer_child_profile_bound hlam hsig hkap hkap1 hgap hloss
    (half_pos heta) (2*n) hΨ hpos hs hone
  obtain ⟨N₂,h₂⟩ := uniform_actual_distance_equation12 hsig
    (by linarith : 10*sig < kap) Real.pi_pos (by linarith [Real.pi_pos])
    (2*n) lam T hlam hT (half_pos heta) hJ hΨ hpos hs
  refine ⟨max N₁ N₂,lt_of_lt_of_le hN₁ (le_max_left _ _),?_⟩
  intro N hN Q ρ mass hQ hcarry hlo hhi B δ hprof c hw hc hc2
  let : ∀ l, IsProbabilityMeasure (ρ l) := fun l => (hprof l).probability
  let q := sourcePolicyBlock N kap
  let J := sourceSmoothingLevels sig kap
  let A := fun l (t : ℕ) => mass l t-(t:ℝ)/N
  let d := RootShellData.ofOuter (Q 0) (Q 1) (ρ 0) (ρ 1) (mass 0) (mass 1)
    N lam lam sig kap c (Q 0) (Q 1)
  have hNpos : 0 < N := lt_of_lt_of_le hN₁ ((le_max_left _ _).trans hN)
  have hq : 0 < q := sourcePolicyBlock_pos hNpos hkap
  have hsigsmall : sig < 1/1000 := lt_of_lt_of_le hgap (by linarith)
  have hbound : ∀ j ∈ Finset.range (n+1), ∀ b ∈ inverseLeibnizTerms j d.indices, ∀ ξ,
      d.inversePhasedHF N Ψ b.2 ξ ≠ ⊤ ∧
      (d.inversePhasedHF N Ψ b.2 ξ).toReal ≤
        ((2:ℝ)^N)^(min (height (A 0) 0 c) (height (A 1) 0 c)-
          (potential (A 0) c N (10*q)+potential (A 1) c N (10*q))/2+
          500*kap+10^6*(lam+sig)/kap+4000*(lam+sig)+eta)+((2:ℝ)^N)^(-T) := by
    intro j hj b hb ξ
    let k : Fin 2 → PolicyDescriptor → ℕ := ![(fun b' => b.2 (.inl b')),(fun b' => b.2 (.inr b'))]
    let h : Fin 2 → Plane → ℂ := fun _ => spatialFourierPhase 1 ξ
    have hh (l : Fin 2) : Measurable (h l) := by unfold h spatialFourierPhase; fun_prop
    have hhb (l : Fin 2) (x : Plane) : ‖h l x‖ ≤ 1 := by simp [h,spatialFourierPhase_norm]
    have hjn : j ≤ n := by have := Finset.mem_range.mp hj; omega
    have hbudget := root_assignment_budgets d.left d.right b.2 (2*n)
      ((inverseLeibnizTerms_budget j d.indices hb).trans (Nat.mul_le_mul_left 2 hjn))
    have hk (l : Fin 2) : ∑ b' ∈ outerDescriptorList (mass l) N q c, k l b' ≤ 2*n := by
      fin_cases l
      · exact hbudget.1
      · exact hbudget.2
    have hchild := h₁ N ((le_max_left _ _).trans hN) Q ρ mass hQ hcarry B δ hprof c hw k hk h hh hhb
    have hcard (l : Fin 2) : (outerDescriptorList (mass l) N q c).card ≤ (N+1)^3+1 :=
      outerDescriptorList_card _ hq
    have hlength (l : Fin 2) (b' : PolicyDescriptor) (hb' : b' ∈ outerDescriptorList (mass l) N q c) :
        descriptorLength (id b') ≤ N/2 := outerDescriptorList_half _ hq hc2 hb'
    have hcR : 2*(c:ℝ) ≤ N := by exact_mod_cast hc2
    have hhalfR : (N/2:ℕ) ≤ (N:ℝ)/2 := by
      have hh' : 2*(N/2) ≤ N := by omega
      have hh'' : 2*((N/2:ℕ):ℝ) ≤ (N:ℝ) := by exact_mod_cast hh'
      linarith
    have hgraph := h₂ N ((le_max_right _ _).trans hN)
      (fun l => outerDescriptorList (mass l) N q c) (fun _ => id) k hcard hk
      (N/2) hlength Q hQ ρ mass B δ hprof 0 h hJ hh hhb 0 c N
      (by omega) hc
      (by simp only [Nat.cast_zero,zero_add]; nlinarith [mul_nonneg (show 0 ≤ 1/1000-sig by linarith) (Nat.cast_nonneg (α := ℝ) N)])
      (by simp only [Nat.cast_zero,zero_add]; nlinarith [mul_nonneg hsig.le (Nat.cast_nonneg (α := ℝ) N)])
      (by simp only [Nat.cast_zero,zero_add]; nlinarith [mul_nonneg hsig.le (Nat.cast_nonneg (α := ℝ) N)])
      (by simp)
      (fun _ => .parallel 0 c) (fun _ => Finset.mem_insert_self _ _)
      (fun _ => by simp) [] [] rfl rfl (by simpa [DyadicSquare.descendant] using hlo) (by simpa [DyadicSquare.descendant] using hhi)
    have hzero (l : Fin 2) : mass l 0 = 0 := (hprof l).zero
    have hleft : spatialPhasedSymbol 1 ξ (d.endpointLeft b.2) =
        inheritedCircleSymbol (outerDescriptorList (mass 0) N q c) id (k 0)
          (Q 0) (ρ 0) (mass 0) N lam sig J 0 (h 0) := by
      funext x dir
      dsimp only [d,RootShellData.ofOuter,RootShellData.endpointLeft,rootLeftSymbol,
        RootEndpointData.ofOuter,RootEndpointData.symbol]
      rw [spatialPhased_inherited]
      simp only [mul_one]
      rfl
    have hright : spatialPhasedSymbol 1 ξ (d.endpointRight b.2) =
        inheritedCircleSymbol (outerDescriptorList (mass 1) N q c) id (k 1)
          (Q 1) (ρ 1) (mass 1) N lam sig J 0 (h 1) := by
      funext x dir
      dsimp only [d,RootShellData.ofOuter,RootShellData.endpointRight,rootRightSymbol,
        RootEndpointData.ofOuter,RootEndpointData.symbol]
      rw [spatialPhased_inherited]
      simp only [mul_one]
      rfl
    have henergy : d.inversePhasedHF N Ψ b.2 ξ =
        sourceParentHF 0 N Ψ (Q 0) (Q 1) (ρ 0) (ρ 1) 1 1
          (inheritedCircleSymbol (outerDescriptorList (mass 0) N q c) id (k 0)
            (Q 0) (ρ 0) (mass 0) N lam sig J 0 (h 0))
          (inheritedCircleSymbol (outerDescriptorList (mass 1) N q c) id (k 1)
            (Q 1) (ρ 1) (mass 1) N lam sig J 0 (h 1)) := by
      unfold RootShellData.inversePhasedHF
      rw [hleft,hright]
      rfl
    dsimp only at hgraph hchild
    simp only [Nat.cast_zero,zero_add,sub_zero,hzero,neg_zero,Real.rpow_zero,
      zero_div,DyadicSquare.descendant] at hgraph
    rw [henergy]
    refine ⟨hgraph.1,hgraph.2.trans ?_⟩
    have hmax := hchild.2 (sourceProductVertices (Q 0) (Q 1) (ρ 0) (ρ 1) [] [] c) (by
      intro row hr
      have hv := sourceProductVertices_subset (Q 0) (Q 1) (ρ 0) (ρ 1) [] [] 0 c rfl rfl hr
      simpa only [Nat.zero_add,Finset.mem_product,mem_dyadicPaths] using hv)
    calc
      _ ≤ ((2:ℝ)^N)^(-A 0 c-A 1 c+min (height (A 0) 0 c) (height (A 1) 0 c)+4000*(lam+sig)+eta/2) *
          ((2:ℝ)^N)^(A 0 c+A 1 c-
            (potential (A 0) c N (10*q)+potential (A 1) c N (10*q))/2+
            500*kap+10^6*(lam+sig)/kap+eta/2)+((2:ℝ)^N)^(-T) := by
        exact add_le_add (mul_le_mul_of_nonneg_left hmax (by positivity)) le_rfl
      _ = _ := by rw [← Real.rpow_add (by positivity)]; congr 2; ring
  refine ⟨hbound,?_⟩
  exact d.inverseShellSupremum_le n N Ψ (by positivity) (fun j hj b hb ξ => (hbound j hj b hb ξ).2)

end PlanarFalconer

end OAI
