import OAI.NumberTheory.TotientAsymptotic.LocallyConcentratedFamily

namespace OAI

/-! Turning buffered concentration into geometric upper bounds at every index. -/
noncomputable section
open scoped Topology
open Filter
namespace TotientAsymptotic

lemma localCoordinateCap_geometric {n m : ℕ} {B A : ℝ} (hn : 0 < n)
    (hnm : n ≤ m) (hA : 0 < A) (hscale : B*rho^m/(n:ℝ) ≤ A)
    (hB : 0 ≤ B) (i : Fin n) :
    localCoordinateCap n B i ≤ 2*A*(m-i.val:ℕ)*(rho^(m-i.val))⁻¹ := by
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have hpow : rho^(i.val+1)*rho^(m-i.val)=rho^m*rho := by
    rw [←pow_add,show i.val+1+(m-i.val)=m+1 by have := i.isLt; omega,pow_succ]
  have he : localCoordinateCap n B i*rho^(m-i.val) =
      2*(B*rho^m/(n:ℝ))*rho*(n-i.val:ℕ) := by
    unfold localCoordinateCap
    calc
      _ = (2*B*(n-i.val:ℕ)/(n:ℝ))*(rho^(i.val+1)*rho^(m-i.val)) := by ring
      _ = _ := by rw [hpow]; ring
  have hdim : ((n-i.val:ℕ):ℝ) ≤ (m-i.val:ℕ) := by
    exact_mod_cast Nat.sub_le_sub_right hnm i.val
  have hs0 : 0 ≤ B*rho^m/(n:ℝ) := div_nonneg (mul_nonneg hB (pow_pos rho_pos _).le) hn'.le
  have hr : (B*rho^m/(n:ℝ))*rho ≤ A :=
    (mul_le_of_le_one_right hs0 rho_lt_one.le).trans hscale
  have hb : 2*((B*rho^m/(n:ℝ))*rho)*(n-i.val:ℕ) ≤
      2*A*(m-i.val:ℕ) := by
    apply mul_le_mul (mul_le_mul_of_nonneg_left hr (by norm_num)) hdim
    · exact Nat.cast_nonneg _
    · positivity
  change localCoordinateCap n B i ≤ (2*A*(m-i.val:ℕ))/rho^(m-i.val)
  apply (le_div_iff₀ (pow_pos rho_pos _)).mpr
  rw [he]
  nlinarith only [hb]

lemma locally_concentrated_all_coordinates {m n L : ℕ} {B c A : ℝ}
    (hL : L+2 ≤ n) (hnm : n ≤ m) (hB : 0 ≤ B) (hA : 0 < A)
    (hscale : B*rho^m/(n:ℝ) ≤ A)
    {u : Fin n → ℝ} (hu : u ∈ locallyConcentratedFamily m n B c L) :
    ∀ i : Fin n,u i ≤
      2*A*(m-i.val+L+2:ℕ)*(rho^(m-i.val+L+2))⁻¹ := by
  intro i
  let j : Fin n := ⟨min i.val (n-(L+2)),by omega⟩
  have hji : j ≤ i := by show j.val ≤ i.val; exact min_le_left _ _
  have hjL : j.val+L+2 ≤ n := by
    have hh : j.val ≤ n-(L+2) := min_le_right _ _
    omega
  have horder : u i ≤ u j := hu.1.1.1.2.1.antitone hji
  have hcap := hu.2 j hjL
  have hgeo := localCoordinateCap_geometric (by omega) hnm hA hscale hB j
  have hdist : m-j.val ≤ m-i.val+L+2 := by
    dsimp [j]
    have := i.isLt
    omega
  have hd := index_inv_pow_mono hdist
  exact horder.trans (hcap.trans (hgeo.trans (by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hd (show 0 ≤ 2*A by positivity))))

theorem local_candidate_coordinate_envelope : ∃ A : ℝ,0 < A ∧
    ∀ H L : ℕ,∀ᶠ x : ℝ in atTop,∀ c : ℝ,
      ∀ u ∈ locallyConcentratedFamily (m x) (m x-H) (B x) c L,
        ∀ i : Fin (m x-H),u i ≤
          A*(m x-i.val+L+2:ℕ)*(rho^(m x-i.val+L+2))⁻¹ := by
  obtain ⟨A,hA,hscale⟩ := natural_coordinate_scale_upper
  refine ⟨2*A,by positivity,?_⟩
  intro H L
  filter_upwards [hscale H,m_tendsto.eventually (eventually_ge_atTop (H+L+2)),
    B_tendsto.eventually (eventually_ge_atTop (0:ℝ))] with x hx hm hB
  intro c u hu i
  exact locally_concentrated_all_coordinates (by omega) (Nat.sub_le _ _) hB hA hx.2 hu i

end TotientAsymptotic

end

end OAI
