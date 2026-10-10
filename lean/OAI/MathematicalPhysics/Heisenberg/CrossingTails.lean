import OAI.MathematicalPhysics.Heisenberg.SparseCrossings

namespace OAI

noncomputable section

open scoped Classical
open scoped Classical BigOperators

namespace Heisenberg.Geometry
lemma scaled_ball_card (d b n : ℕ) (hb : 1 ≤ b) (z : Site d) :
    (ballFinset d (16*b^n+8) z).card ≤ 49^d*(b^d)^n := by
  rw [ballFinset_card]
  have hp : 1 ≤ b^n := one_le_pow₀ hb
  have h : 2*(16*b^n+8)+1 ≤ 49*b^n := by omega
  calc
    _ ≤ (49*b^n)^d := Nat.pow_le_pow_left h _
    _ = _ := by rw [mul_pow]; congr 1; rw [←pow_mul,←pow_mul,Nat.mul_comm]

theorem lattice_crossing_mass_bound {Ω : Type*} [Fintype Ω]
    (d b : ℕ) (hb : 100 ≤ b) (α L : ℝ) (hα : 0 ≤ α) (hL : 1 ≤ L)
    (hba : 2 ≤ (b:ℝ)^α)
    (μ : Ω → ℝ) (hμ : ∀ ω, 0 ≤ μ ω) (Z : Ω → Set (Site d))
    (q : ℝ) (hq : 0 ≤ q)
    (htest : ∀ F : Finset (Site d), SparseWitness.Sparse α L F →
      (∑ ω, if (F:Set (Site d)) ⊆ Z ω then μ ω else 0) ≤ q^F.card)
    (n : ℕ) (z : Site d) :
    (∑ ω, if SparseWitness.Crosses (Z ω) z (16*(b:ℝ)^n) then μ ω else 0) ≤
      (((49^d*(b^d)^2:ℕ):ℝ)*q)^(2^n) := by
  have hb1 : 1 ≤ b := by omega
  have hbR : 1 ≤ (b:ℝ) := by exact_mod_cast hb1
  apply SparseWitness.crossing_mass_bound μ hμ Z (fun j => 16*(b:ℝ)^j)
    (fun j => by positivity) (fun j => SparseWitness.geometric_scale_gap _ (by exact_mod_cast hb) j)
    α L hα hL (SparseWitness.geometric_scale_growth _ _ hbR hα hba)
    (fun j z => ballFinset d (16*b^j+8) z) _ (49^d) (b^d)
    (one_le_pow₀ (by omega)) (one_le_pow₀ hb1) _ q hq htest
  · intro j x y hxy
    apply (mem_ballFinset ..).mpr
    apply (dist_le_iff_mem_ball x y).mp
    norm_cast at hxy ⊢
  · intro j x
    exact scaled_ball_card d b (j+1) hb1 x

end Heisenberg.Geometry

namespace Heisenberg.SparseWitness
variable {V Ω : Type*} [PseudoMetricSpace V] [Fintype Ω]

lemma Crosses.mono_radius {Z : Set V} {z : V} {r s : ℝ} (h : Crosses Z z r)
    (hs : s ≤ r) : Crosses Z z s := by
  obtain ⟨p,m,hp,hz,hstep,hr⟩ := h
  exact ⟨p,m,hp,hz,hstep,hs.trans hr⟩

lemma event_mass_mono (μ : Ω → ℝ) (hμ : ∀ ω, 0 ≤ μ ω)
    {A B : Ω → Prop} (hAB : ∀ ω, A ω → B ω) :
    (∑ ω, if A ω then μ ω else 0) ≤ ∑ ω, if B ω then μ ω else 0 := by
  apply Finset.sum_le_sum
  intro ω _
  by_cases ha : A ω
  · rw [ite_eq_left ha,ite_eq_left (hAB ω ha)]
  · rw [ite_eq_right ha]
    split_ifs <;> simp [hμ]

theorem stretched_tail_of_scales (μ : Ω → ℝ) (hμ : ∀ ω, 0 ≤ μ ω)
    (hprob : ∑ ω, μ ω ≤ 1) (Z : Ω → Set V) (b γ : ℝ)
    (hb : 1 < b) (hγ : 0 < γ) (hbγ : b^γ = 2)
    (htail : ∀ n z, (∑ ω, if Crosses (Z ω) z (16*b^n) then μ ω else 0) ≤
      Real.exp (-2*(2:ℝ)^n)) (z : V) (r : ℝ) (hr : 0 ≤ r) :
    (∑ ω, if Crosses (Z ω) z r then μ ω else 0) ≤
      Real.exp 1 * Real.exp (-((r/(16*b))^γ)) := by
  by_cases hrs : r < 16
  · have hbase : r/(16*b) ≤ 1 := (div_le_one (by positivity)).mpr (by nlinarith)
    have hpow : (r/(16*b))^γ ≤ 1 := Real.rpow_le_one (by positivity) hbase hγ.le
    calc
      _ ≤ ∑ ω, μ ω := Finset.sum_le_sum (fun ω _ => by split_ifs <;> simp [hμ])
      _ ≤ 1 := hprob
      _ ≤ Real.exp 1*Real.exp (-((r/(16*b))^γ)) := by
        rw [←Real.exp_add]
        exact Real.one_le_exp (by linarith)
  · obtain ⟨n,hnl,hnr⟩ := exists_nat_pow_near (x:=r/16) (by linarith) hb
    have hnr' : r/(16*b) ≤ b^n := by
      apply (div_le_iff₀ (by positivity)).mpr
      rw [pow_succ] at hnr
      nlinarith
    have hp : (r/(16*b))^γ ≤ (2:ℝ)^n := by
      calc
        _ ≤ (b^n)^γ := Real.rpow_le_rpow (by positivity) hnr' hγ.le
        _ = (b^γ)^n := by
          rw [← Real.rpow_natCast,← Real.rpow_mul (by linarith),mul_comm,
            Real.rpow_mul (by linarith),Real.rpow_natCast]
        _ = _ := by rw [hbγ]
    calc
      _ ≤ ∑ ω, if Crosses (Z ω) z (16*b^n) then μ ω else 0 :=
        event_mass_mono μ hμ (fun _ h => h.mono_radius (by linarith))
      _ ≤ Real.exp (-2*(2:ℝ)^n) := htail n z
      _ ≤ Real.exp (-((r/(16*b))^γ)) := Real.exp_le_exp.mpr (by nlinarith [pow_nonneg (show (0:ℝ) ≤ 2 by norm_num) n])
      _ ≤ Real.exp 1 * Real.exp (-((r/(16*b))^γ)) := by
        simpa using mul_le_mul_of_nonneg_right (Real.one_le_exp (by norm_num : (0:ℝ) ≤ 1))
          (Real.exp_nonneg (-((r/(16*b))^γ)))

lemma exists_scale_exponent {b : ℝ} (hb : 1 < b) :
    ∃ γ : ℝ, 0 < γ ∧ b^γ = 2 := by
  refine ⟨Real.log 2/Real.log b,div_pos (Real.log_pos (by norm_num)) (Real.log_pos hb),?_⟩
  rw [Real.rpow_def_of_pos (by linarith)]
  have hlog : Real.log b ≠ 0 := ne_of_gt (Real.log_pos hb)
  rw [mul_div_cancel₀ _ hlog,Real.exp_log (by norm_num : (0:ℝ) < 2)]

lemma sparse_of_card_le {α L : ℝ} (hα : 0 ≤ α) (hL : 0 ≤ L) (F : Finset V)
    (hF : (F.card:ℝ) ≤ L) : Sparse α L F := by
  intro z r hr
  calc
    _ ≤ (F.card:ℝ) := by exact_mod_cast Finset.card_filter_le F _
    _ ≤ L := hF
    _ ≤ L*(1+r)^α := by
      simpa using mul_le_mul_of_nonneg_left (Real.one_le_rpow (by linarith) hα) hL

lemma countable_union_mass {W : Type*} (μ : Ω → ℝ) (hμ : ∀ ω, 0 ≤ μ ω)
    (E : W → Ω → Prop) (A : Ω → Prop) (g : W → ℝ)
    (hg : ∀ w, 0 ≤ g w) (hs : Summable g)
    (hE : ∀ w, (∑ ω, if E w ω then μ ω else 0) ≤ g w)
    (hA : ∀ ω, A ω → ∃ w, E w ω) :
    (∑ ω, if A ω then μ ω else 0) ≤ ∑' w, g w := by
  let S := Finset.univ.filter A
  let pick (ω : S) : W := Classical.choose (hA ω (Finset.mem_filter.mp ω.property).2)
  let F : Finset W := S.attach.image pick
  have hcover : ∀ ω, A ω → ∃ w ∈ F, E w ω := by
    intro ω hω
    let a : S := ⟨ω,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hω⟩⟩
    refine ⟨pick a, Finset.mem_image.mpr ⟨a,Finset.mem_attach _ _,rfl⟩,?_⟩
    exact Classical.choose_spec (hA ω hω)
  calc
    _ ≤ ∑ w ∈ F, ∑ ω, if E w ω then μ ω else 0 := finite_union_mass μ hμ F E A hcover
    _ ≤ ∑ w ∈ F, g w := Finset.sum_le_sum (fun w _ => hE w)
    _ ≤ ∑' w, g w := hs.sum_le_tsum F (fun w _ => hg w)

theorem bad_count_mass (μ : Ω → ℝ) (hμ : ∀ ω, 0 ≤ μ ω) (Z : Ω → Set V)
    (α L p : ℝ) (hα : 0 ≤ α) (hL : 0 ≤ L) (k : ℕ) (hk : (k:ℝ) ≤ L)
    (htest : ∀ F : Finset V, Sparse α L F →
      (∑ ω, if (F:Set V) ⊆ Z ω then μ ω else 0) ≤ p^F.card)
    (B : Finset V) :
    (∑ ω, if k ≤ (B.filter (· ∈ Z ω)).card then μ ω else 0) ≤
      (B.card.choose k:ℝ)*p^k := by
  have hcover : ∀ ω, k ≤ (B.filter (· ∈ Z ω)).card →
      ∃ F ∈ B.powersetCard k, (F:Set V) ⊆ Z ω := by
    intro ω hω
    obtain ⟨F,hF,hcard⟩ := Finset.exists_subset_card_eq hω
    refine ⟨F,Finset.mem_powersetCard.mpr ⟨hF.trans (Finset.filter_subset ..),hcard⟩,?_⟩
    intro v hv
    exact (Finset.mem_filter.mp (hF hv)).2
  calc
    _ ≤ ∑ F ∈ B.powersetCard k, ∑ ω, if (F:Set V) ⊆ Z ω then μ ω else 0 :=
      by
        convert finite_union_mass μ hμ (B.powersetCard k) (fun F ω => (F:Set V) ⊆ Z ω) (fun ω => k ≤ (B.filter (· ∈ Z ω)).card) hcover using 1
        apply Finset.sum_congr rfl
        intro ω _
        split_ifs <;> rfl
    _ ≤ ∑ _F ∈ B.powersetCard k, p^k := by
      apply Finset.sum_le_sum
      intro F hF
      have hc := (Finset.mem_powersetCard.mp hF).2
      simpa only [hc] using htest F (sparse_of_card_le hα hL F (by simpa only [hc] using hk))
    _ = _ := by simp

end Heisenberg.SparseWitness

open scoped Classical
open Module

open scoped BigOperators
namespace Heisenberg.Stretched

lemma exp_power_bound (c ξ t : ℝ) (hc : 0 < c) (ht : 0 < t) (n : ℕ) :
    Real.exp (-c*t^ξ) ≤ (n.factorial:ℝ)/c^n * t^(-ξ*(n:ℝ)) := by
  have hct : 0 < c*t^ξ := mul_pos hc (Real.rpow_pos_of_pos ht ξ)
  have hf : 0 < (n.factorial:ℝ) := by exact_mod_cast Nat.factorial_pos n
  have hh := Real.pow_div_factorial_le_exp (c*t^ξ) hct.le n
  have hi := (one_div_le_one_div_of_le (div_pos (pow_pos hct n) hf) hh)
  have he : (1:ℝ) / ((c*t^ξ)^n/(n.factorial:ℝ)) =
      (n.factorial:ℝ)/c^n * t^(-ξ*(n:ℝ)) := by
    rw [mul_pow]
    rw [← Real.rpow_natCast (t^ξ) n, ← Real.rpow_mul ht.le]
    rw [neg_mul,Real.rpow_neg ht.le]
    field_simp
  rw [he] at hi
  simpa only [one_div,←Real.exp_neg,neg_mul] using hi

theorem exists_polynomial_envelope (c ξ r : ℝ) (hc : 0 < c) (hξ : 0 < ξ) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 1 ≤ t → Real.exp (-c*t^ξ) ≤ C*t^(-r) := by
  obtain ⟨n,hn⟩ := exists_nat_gt (r/ξ)
  have hnr : r ≤ ξ*(n:ℝ) := by
    have := (div_lt_iff₀ hξ).mp hn
    nlinarith
  refine ⟨(n.factorial:ℝ)/c^n,div_pos (by exact_mod_cast Nat.factorial_pos n) (pow_pos hc n),?_⟩
  intro t ht
  exact (exp_power_bound c ξ t hc (by linarith) n).trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le ht (by linarith)) (by positivity))

end Heisenberg.Stretched

namespace Heisenberg.LatticeSum
open Heisenberg.Geometry

lemma radius_eq_norm {k : ℕ} (x : Site (k+1)) : (radius x : ℝ) = ‖x‖ := by
  apply le_antisymm
  · obtain ⟨j,hj,he⟩ := Finset.exists_mem_eq_sup Finset.univ (Finset.univ_nonempty) (fun j : Fin (k+1) => (x j).natAbs)
    change ((Finset.univ.sup (fun j => (x j).natAbs) : ℕ) : ℝ) ≤ ‖x‖
    rw [he]
    simpa only [Int.norm_eq_abs,Nat.cast_natAbs,Int.cast_abs] using norm_le_pi_norm x j
  · apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro j
    have h : (x j).natAbs ≤ radius x := Finset.le_sup (f:=fun j => (x j).natAbs) (Finset.mem_univ j)
    simpa only [Int.norm_eq_abs,Nat.cast_natAbs,Int.cast_abs] using (show ((x j).natAbs : ℝ) ≤ (radius x : ℝ) by exact_mod_cast h)

lemma uniform_polynomial_sum (k : ℕ) (r : ℝ) (hr : r < -(k+1:ℝ)) :
    ∃ M ≥ 0, ∀ y : Site (k+1), Summable (fun x => (1+dist x y)^r) ∧
      (∑' x, (1+dist x y)^r) = M := by
  let M := ∑' x : Site (k+1), ((radius x:ℝ)+1)^r
  refine ⟨M,tsum_nonneg (fun x => Real.rpow_nonneg (by positivity) _),?_⟩
  intro y
  have hs := summable_radius_sub_rpow (k+1) r (by push_cast; exact hr) y
  have he := (Equiv.subRight y).tsum_eq (fun x : Site (k+1) => ((radius x:ℝ)+1)^r)
  refine ⟨?_,?_⟩
  · simpa only [radius_eq_norm,dist_eq_norm,add_comm (1:ℝ)] using hs
  · simpa only [M,Equiv.subRight_apply,radius_eq_norm,dist_eq_norm,add_comm (1:ℝ)] using he

theorem exp_tail_polynomial (k : ℕ) (c ξ a : ℝ) (hc : 0 < c) (hξ : 0 < ξ)
    (ha : 0 ≤ a) :
    ∃ C ≥ 0, ∀ (y : Site (k+1)) (R : ℝ), 0 ≤ R →
      Summable (fun x => if R < dist x y then Real.exp (-c*(1+dist x y)^ξ) else 0) ∧
      (∑' x, if R < dist x y then Real.exp (-c*(1+dist x y)^ξ) else 0) ≤ C*(1+R)^(-a) := by
  obtain ⟨D,hD,hpoly⟩ := Heisenberg.Stretched.exists_polynomial_envelope c ξ (a+(k+2:ℝ)) hc hξ
  obtain ⟨M,hM,hMsum⟩ := uniform_polynomial_sum k (-(k+2:ℝ)) (by linarith)
  refine ⟨D*M,mul_nonneg hD.le hM,?_⟩
  intro y R hR
  let F : Site (k+1) → ℝ := fun x => if R < dist x y then Real.exp (-c*(1+dist x y)^ξ) else 0
  let G : Site (k+1) → ℝ := fun x => (D*(1+R)^(-a))*(1+dist x y)^(-(k+2:ℝ))
  have hsG : Summable G := (hMsum y).1.mul_left _
  have hFG : ∀ x, F x ≤ G x := by
    intro x
    dsimp [F,G]
    split_ifs with hx
    · have hp := hpoly (1+dist x y) (by linarith [dist_nonneg (x:=x) (y:=y)])
      have hdec : (1+dist x y)^(-a) ≤ (1+R)^(-a) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
      have he : (1+dist x y)^(-(a+(k+2:ℝ))) =
          (1+dist x y)^(-a)*(1+dist x y)^(-(k+2:ℝ)) := by
        rw [←Real.rpow_add (by positivity)]
        congr 1
        ring
      rw [he] at hp
      exact hp.trans (by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hdec (by positivity)) hD.le)
    · positivity
  have hsF : Summable F := Summable.of_nonneg_of_le (fun x => by dsimp [F]; split_ifs <;> positivity) hFG hsG
  refine ⟨hsF,?_⟩
  calc
    (∑' x, F x) ≤ ∑' x, G x := hsF.tsum_le_tsum hFG hsG
    _ = D*(1+R)^(-a)*M := by rw [tsum_mul_left,(hMsum y).2]
    _ = _ := by ring
end Heisenberg.LatticeSum

end

end OAI
