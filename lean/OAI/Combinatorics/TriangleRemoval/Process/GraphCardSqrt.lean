import Mathlib
import OAI.Combinatorics.TriangleRemoval.Spectral.GlobalLinkAdjacencyHermitian
import OAI.Combinatorics.TriangleRemoval.Tracking.PrefixSpectralErrorPower
import OAI.Combinatorics.TriangleRemoval.Process.PerturbationPolynomialBound

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave
open Filter
open scoped Matrix.Norms.Operator

lemma graph_card_sqrt_le {n : ℕ} {G : Graph n} (h : G ⊆ completeGraph n) :
    Real.sqrt G.card ≤ n := by
  apply (Real.sqrt_le_left (Nat.cast_nonneg n)).mpr
  have hh := Finset.card_le_card h
  rw [card_completeGraph,Nat.choose_two_right] at hh
  have h' : G.card ≤ n*n := hh.trans ((Nat.div_le_self _ _).trans
    (Nat.mul_le_mul_left n (Nat.sub_le n 1)))
  simpa only [Nat.cast_mul,pow_two] using (Nat.cast_le.mpr h' : (G.card : ℝ) ≤ (n*n : ℕ))

lemma goodPrefix_neighbors_nonempty {n : ℕ} (hn : 0 < n) {c C : ℝ} {G : Graph n}
    (h : GoodPrefixGraph n c C G) (hp : 0 < prefixDensity n)
    (hδ : (n : ℝ)^(-c) ≤ 1/2) : ∀ u, (neighbors G u).Nonempty := by
  intro u
  have hnp : 0 < (n : ℝ)*prefixDensity n := mul_pos (Nat.cast_pos.mpr hn) hp
  have hl := (abs_le.mp (h.2.2.1 u)).1
  have hm := mul_le_mul_of_nonneg_right hδ hnp.le
  have hd : (0 : ℝ) < (currentDegree G u : ℝ) := by linarith
  apply Finset.card_pos.mp
  exact_mod_cast hd

theorem goodPrefix_uniform_semigroup {c : ℝ} (hc : 0 < c) :
    ∃ C₁ : ℝ, 0 < C₁ ∧ ∃ J : ℕ, ∀ᶠ n : ℕ in atTop,
      ∀ (C : ℝ) (G : Graph n) (h : GoodPrefixGraph n c C G),
      ∀ s ∈ Set.Icc (0 : ℝ) (Real.log n),
        ‖NormedSpace.exp ((-s) • ((prefixD n)⁻¹ • globalLinkAdjacency G h.1))‖ ≤
          C₁*(1+Real.log n)^J := by
  obtain ⟨γ,hγ,hdec⟩ := prefixSpectralError_power_decay hc
  obtain ⟨K,hK⟩ := exists_nat_gt (4/γ)
  let A : ℝ := 2*(K : ℝ)*12^K
  have hA : 0 ≤ A := by dsimp [A]; positivity
  refine ⟨A+1,by linarith,2*K+1,?_⟩
  have hδ := ((tendsto_rpow_neg_atTop hc).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_le_const
      (by norm_num : (0 : ℝ) < 1/2)
  filter_upwards [hdec,spectral_remainder_eventual hγ K hK.le,
    prefix_scales_eventually_pos,hδ,eventually_ge_atTop (1 : ℕ)] with n hd hr hp hδ hn
  intro C G h s hs
  change (n : ℝ)^(-c) ≤ 1/2 at hδ
  have hn0 : 0 < n := by omega
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog : 0 ≤ Real.log n := Real.log_nonneg hn1
  have : NeZero n := ⟨by omega⟩
  have hne := goodPrefix_neighbors_nonempty hn0 h hp.1 hδ
  have : Nonempty G := by
    obtain ⟨v,hv⟩ := hne ⟨0,hn0⟩
    exact ⟨⟨{⟨0,hn0⟩,v},(Finset.mem_filter.mp hv).2⟩⟩
  have he0 : 0 ≤ 2*prefixSpectralError n c := mul_nonneg (by norm_num)
    (prefixSpectralError_nonneg n c (by linarith [hp.2]))
  have hrem : Real.sqrt G.card *((2*prefixSpectralError n c*Real.log n)^K *
      Real.exp (Real.log n*(2*prefixSpectralError n c))) ≤ 1 :=
    (mul_le_mul_of_nonneg_right (graph_card_sqrt_le h.1) (by positivity)).trans
      (hr _ he0 hd)
  have hb := goodPrefix_semigroup_quantitative h hne hp.2 (by linarith)
    (Real.log n) hlog K s hs
  have hh := perturbation_polynomial_bound (Real.log n) hlog K
  have h1 : (1 : ℝ) ≤ (1+Real.log n)^(2*K+1) :=
    one_le_pow₀ (by linarith)
  calc
    _ ≤ A*(1+Real.log n)^(2*K+1)+1 := by dsimp [A]; linarith
    _ ≤ (A+1)*(1+Real.log n)^(2*K+1) := by nlinarith

end SharpTerminalLeave

end

end OAI
