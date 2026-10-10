import OAI.MathematicalPhysics.Heisenberg.CrossingTails

namespace OAI

noncomputable section

open scoped Classical
open scoped Classical BigOperators
open scoped Classical
open Module
open scoped BigOperators

namespace Heisenberg.Geometry
open Heisenberg.SparseWitness

theorem lattice_stretched_tail {Ω : Type*} [Fintype Ω]
    (d b : ℕ) (hb : 100 ≤ b) (α L : ℝ) (hα : 0 ≤ α) (hL : 1 ≤ L)
    (hba : 2 ≤ (b:ℝ)^α) (μ : Ω → ℝ) (hμ : ∀ ω, 0 ≤ μ ω)
    (hprob : ∑ ω, μ ω ≤ 1) (Z : Ω → Set (Site d))
    (q : ℝ) (hq : 0 ≤ q) (hsmall : (((49^d*(b^d)^2:ℕ):ℝ)*q) ≤ Real.exp (-2))
    (htest : ∀ F : Finset (Site d), Sparse α L F →
      (∑ ω, if (F:Set (Site d)) ⊆ Z ω then μ ω else 0) ≤ q^F.card) :
    ∃ c : ℝ, c > 0 ∧ ∃ γ : ℝ, γ > 0 ∧ ∀ z r, 0 ≤ r →
      (∑ ω, if Crosses (Z ω) z r then μ ω else 0) ≤ Real.exp 1*Real.exp (-c*r^γ) := by
  have hbR : (1:ℝ) < b := by exact_mod_cast (show 1 < b by omega)
  obtain ⟨γ,hγ,hbγ⟩ := exists_scale_exponent hbR
  let c := (16*(b:ℝ))^(-γ)
  have hc : 0 < c := Real.rpow_pos_of_pos (by positivity) _
  refine ⟨c,hc,γ,hγ,?_⟩
  intro z r hr
  have hh := stretched_tail_of_scales μ hμ hprob Z (b:ℝ) γ hbR hγ hbγ ?_ z r hr
  · convert hh using 1
    rw [Real.div_rpow hr (by positivity)]
    dsimp [c]
    rw [Real.rpow_neg (by positivity)]
    ring_nf
  · intro n z
    calc
      _ ≤ (((49^d*(b^d)^2:ℕ):ℝ)*q)^(2^n) := lattice_crossing_mass_bound d b hb α L hα hL hba μ hμ Z q hq htest n z
      _ ≤ (Real.exp (-2))^(2^n) := pow_le_pow_left₀ (by positivity) hsmall _
      _ = Real.exp (-2*(2:ℝ)^n) := by rw [←Real.exp_nat_mul]; congr 1; push_cast; ring

end Heisenberg.Geometry

namespace Heisenberg.LatticeRegular
open Heisenberg.Geometry Heisenberg.LatticeComponents Heisenberg.SparseWitness
variable {d : ℕ}

lemma component_crosses (Z : Set (Site d)) {z w : Site d} (hz : z ∈ Z)
    (hw : w ∈ Component Z z) (r : ℝ) (hr : r ≤ dist z w) : Crosses Z z r := by
  have hp : ∃ (p : ℕ → Site d) (m : ℕ), p 0 = z ∧ p m = w ∧
      (∀ i ≤ m, p i ∈ Z) ∧ (∀ i < m, dist (p i) (p (i+1)) ≤ 8) := by
    have hrel := hw.2
    clear hw hr
    induction hrel with
    | refl => exact ⟨fun _ => z,0,rfl,rfl,fun _ _ => hz,by simp⟩
    | @tail b c hzb hbc ih =>
      obtain ⟨p,m,hp0,hpm,hpZ,hpstep⟩ := ih
      let t : ℕ → Site d := fun i => if i ≤ m then p i else c
      refine ⟨t,m+1,?_,?_,?_,?_⟩
      · simp [t,hp0]
      · simp [t]
      · intro i hi
        by_cases h : i ≤ m
        · simpa [t,h] using hpZ i h
        · simpa [t,h] using hbc.2.2
      · intro i hi
        by_cases h : i < m
        · simpa [t,show i ≤ m by omega,show i+1 ≤ m by omega] using hpstep i h
        · have he : i = m := by omega
          subst i
          simpa [t,hpm] using (dist_le_iff_mem_ball (r:=8) b c).mpr hbc.1
  obtain ⟨p,m,hp0,hpm,hpZ,hpstep⟩ := hp
  exact ⟨p,m,hp0,hpZ,hpstep,by simpa [hp0,hpm] using hr⟩

lemma local_bad_count_bound {Ω : Type*} [Fintype Ω]
    (k M : ℕ) (α L p : ℝ) (hα : 0 ≤ α) (hL : (2*(k+1):ℕ) ≤ L)
    (μ : Ω → ℝ) (Z : Ω → Set (Site (k+1))) (hμ : ∀ ω, 0 ≤ μ ω)
    (htest : ∀ F : Finset (Site (k+1)), Sparse α L F →
      (∑ ω, if (F:Set (Site (k+1))) ⊆ Z ω then μ ω else 0) ≤ p^F.card)
    (x : Site (k+1)) (R : ℕ) :
    (∑ ω, if ∃ z ∈ Ball (11*R:ℕ) x,
      2*(k+1) ≤ ((ballFinset (k+1) M z).filter (· ∈ Z ω)).card then μ ω else 0) ≤
      ((23:ℝ)^(k+1)*(((2*M+1)^(k+1)).choose (2*(k+1)):ℕ)) *
        (1+(R:ℝ))^(k+1)*p^(2*(k+1)) := by
  let B : ℝ := (23:ℝ)^(k+1)*(((2*M+1)^(k+1)).choose (2*(k+1)):ℕ)
  calc
    _ ≤ ∑ z ∈ ballFinset (k+1) (11*R) x,
      ∑ ω, if 2*(k+1) ≤ ((ballFinset (k+1) M z).filter (· ∈ Z ω)).card then μ ω else 0 :=
      by
        rw [Finset.sum_comm]
        apply Finset.sum_le_sum
        intro ω _
        split_ifs with h
        · obtain ⟨z,hz,hh⟩ := h
          have hzm := (mem_ballFinset (k+1) (11*R) x z).mpr hz
          have hs := Finset.single_le_sum (f:=fun z =>
            if 2*(k+1) ≤ ((ballFinset (k+1) M z).filter (· ∈ Z ω)).card then μ ω else 0)
            (fun j _ => by split_ifs <;> simp [hμ]) hzm
          simpa only [ite_eq_left hh] using hs
        · exact Finset.sum_nonneg (fun j _ => by split_ifs <;> simp [hμ])
    _ ≤ ∑ _z ∈ ballFinset (k+1) (11*R) x, ((((2*M+1)^(k+1)).choose (2*(k+1)):ℕ):ℝ)*p^(2*(k+1)) := by
      apply Finset.sum_le_sum
      intro z _
      simpa only [ballFinset_card] using bad_count_mass μ hμ Z α L p hα
        ((by positivity : (0:ℝ) ≤ (2*(k+1):ℕ)).trans hL) (2*(k+1)) hL htest (ballFinset (k+1) M z)
    _ = (((2*(11*R)+1)^(k+1)):ℝ)*(((((2*M+1)^(k+1)).choose (2*(k+1)):ℕ):ℝ)*p^(2*(k+1))) := by simp [ballFinset_card]
    _ ≤ B*(1+(R:ℝ))^(k+1)*p^(2*(k+1)) := by
      have hp : 0 ≤ p^(2*(k+1)) := by rw [pow_mul]; positivity
      have hbase : (2*(11*R)+1:ℕ) ≤ 23*(1+(R:ℝ)) := by push_cast; nlinarith [Nat.cast_nonneg (α:=ℝ) R]
      have hh := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ (2*(11*R)+1:ℕ)) hbase (k+1)
      rw [mul_pow] at hh
      dsimp [B]
      push_cast at hh
      nlinarith [mul_le_mul_of_nonneg_right hh (mul_nonneg (Nat.cast_nonneg (((2*M+1)^(k+1)).choose (2*(k+1)))) hp)]

theorem regularity_bound_of_tail
    (k M : ℕ) (α L ν a c γ : ℝ) (hα : 0 ≤ α) (hL : (2*(k+1):ℕ) ≤ L)
    (hν : 0 < ν) (ha : 0 ≤ a) (hc : 0 < c) (hγ : 0 < γ) :
    ∃ C ≥ 0, ∀ (Ω : Type*) [Fintype Ω] (μ : Ω → ℝ) (Z : Ω → Set (Site (k+1))) (p : ℝ),
      (∀ ω, 0 ≤ μ ω) →
      (∀ F : Finset (Site (k+1)), Sparse α L F →
        (∑ ω, if (F:Set (Site (k+1))) ⊆ Z ω then μ ω else 0) ≤ p^F.card) →
      (∀ z r, 0 ≤ r → (∑ ω, if Crosses (Z ω) z r then μ ω else 0) ≤
        Real.exp 1*Real.exp (-c*r^γ)) →
      ∀ (x : Site (k+1)) (R : ℕ),
        (∑ ω, if ¬ Regular (Z ω) x R M ν then μ ω else 0) ≤
          C*((1+(R:ℝ))^(k+1)*p^(2*(k+1))+(1+(R:ℝ))^(-a)) := by
  obtain ⟨D,hD,hDt⟩ := Heisenberg.LatticeSum.exp_tail_polynomial k c (ν*γ) a hc (mul_pos hν hγ) ha
  let B : ℝ := (23:ℝ)^(k+1)*(((2*M+1)^(k+1)).choose (2*(k+1)):ℕ)
  refine ⟨B+Real.exp 1*D,by dsimp [B]; positivity,?_⟩
  intro Ω inst μ Z p hμ htest htail x R
  let A : Ω → Prop := fun ω => ∃ z ∈ Ball (11*R:ℕ) x,
    2*(k+1) ≤ ((ballFinset (k+1) M z).filter (· ∈ Z ω)).card
  let E : Site (k+1) → Ω → Prop := fun z ω => z ∉ Ball (10*R:ℕ) x ∧
    ∃ w ∈ Component (Z ω) z, (1+dist z x)^ν < dist z w ∧ z ∈ Z ω
  have hA : (∑ ω, if A ω then μ ω else 0) ≤ B*(1+(R:ℝ))^(k+1)*p^(2*(k+1)) :=
    local_bad_count_bound k M α L p hα hL μ Z hμ htest x R
  let G : Site (k+1) → ℝ := fun z => if (R:ℝ) < dist z x then Real.exp (-c*(1+dist z x)^(ν*γ)) else 0
  have ht := hDt x (R:ℝ) (Nat.cast_nonneg R)
  have hsG : Summable G := ht.1
  have hE : ∀ z, (∑ ω, if E z ω then μ ω else 0) ≤ Real.exp 1*G z := by
    intro z
    by_cases hz : (R:ℝ) < dist z x
    · calc
        _ ≤ ∑ ω, if Crosses (Z ω) z ((1+dist z x)^ν) then μ ω else 0 :=
          by
            have hm := event_mass_mono μ hμ (A:=E z) (B:=fun ω => Crosses (Z ω) z ((1+dist z x)^ν)) (by
              intro ω h
              obtain ⟨_,w,hw,hd,hzZ⟩ := h
              exact component_crosses _ hzZ hw _ hd.le)
            convert hm using 1
            apply Finset.sum_congr rfl
            intro ω _
            split_ifs <;> rfl
        _ ≤ Real.exp 1*Real.exp (-c*((1+dist z x)^ν)^γ) :=
          htail z _ (Real.rpow_nonneg (by positivity) _)
        _ = _ := by dsimp [G]; rw [ite_eq_left hz,←Real.rpow_mul (by positivity)]
    · have hempty : ∀ ω, ¬ E z ω := by
        intro ω h
        have hb : dist x z ≤ (10*R:ℕ) := by
          rw [dist_comm]; push_cast; linarith [le_of_not_gt hz,Nat.cast_nonneg (α:=ℝ) R]
        exact h.1 ((dist_le_iff_mem_ball x z).mp hb)
      simp [hempty,G,hz]
  have hremote : (∑ ω, if ∃ z, E z ω then μ ω else 0) ≤ Real.exp 1*D*(1+(R:ℝ))^(-a) := by
    calc
      _ ≤ ∑' z, Real.exp 1*G z := countable_union_mass μ hμ E (fun ω => ∃ z, E z ω)
        (fun z => Real.exp 1*G z) (by intro z; dsimp [G]; split_ifs <;> positivity)
        (hsG.mul_left _) (by
          intro z
          convert hE z using 1
          apply Finset.sum_congr rfl
          intro ω _
          split_ifs <;> rfl) (fun ω h => h)
      _ = Real.exp 1*(∑' z, G z) := tsum_mul_left
      _ ≤ Real.exp 1*(D*(1+(R:ℝ))^(-a)) := mul_le_mul_of_nonneg_left ht.2 (Real.exp_pos _).le
      _ = _ := by ring
  have hsplit : (∑ ω, if ¬ Regular (Z ω) x R M ν then μ ω else 0) ≤
      (∑ ω, if A ω then μ ω else 0)+(∑ ω, if ∃ z, E z ω then μ ω else 0) := by
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro ω _
    have hcover : ¬ Regular (Z ω) x R M ν → A ω ∨ ∃ z, E z ω := by
      intro hh
      dsimp [Regular] at hh
      push Not at hh
      by_cases h : A ω
      · exact Or.inl h
      · right
        have hn : ∀ z ∈ Ball (11*R:ℕ) x, ((ballFinset (k+1) M z).filter (· ∈ Z ω)).card < 2*(k+1) := by
          intro z hz
          exact lt_of_not_ge (fun hh => h ⟨z,hz,hh⟩)
        obtain ⟨z,hz,hzn,w,hw,hd⟩ := hh hn
        exact ⟨z,hzn,w,hw,hd,hz⟩
    split_ifs <;> try linarith [hμ ω]
    exact False.elim (by rcases hcover ‹¬ Regular (Z ω) x R M ν› with h | h <;> contradiction)
  calc
    _ ≤ B*(1+(R:ℝ))^(k+1)*p^(2*(k+1))+Real.exp 1*D*(1+(R:ℝ))^(-a) := hsplit.trans (add_le_add hA hremote)
    _ ≤ _ := by
      have hp : 0 ≤ p^(2*(k+1)) := by rw [pow_mul]; positivity
      have hB : 0 ≤ B := by dsimp [B]; positivity
      nlinarith [mul_nonneg hB (Real.rpow_nonneg (by positivity : (0:ℝ) ≤ 1+(R:ℝ)) (-a)),
        mul_nonneg (mul_nonneg (Real.exp_pos 1).le hD) (mul_nonneg (pow_nonneg (by positivity : (0:ℝ) ≤ 1+(R:ℝ)) (k+1)) hp)]

theorem regularity_probability (k M b : ℕ) (hb : 100 ≤ b)
    (α L ν a : ℝ) (hα : 0 ≤ α) (hL : (2*(k+1):ℕ) ≤ L)
    (hba : 2 ≤ (b:ℝ)^α) (hν : 0 < ν) (ha : 0 ≤ a) :
    ∃ p₀ > 0, ∃ C ≥ 0, ∀ (Ω : Type*) [Fintype Ω]
      (μ : Ω → ℝ) (Z : Ω → Set (Site (k+1))) (p : ℝ),
      (∀ ω, 0 ≤ μ ω) → (∑ ω, μ ω ≤ 1) → 0 ≤ p → p ≤ p₀ →
      (∀ F : Finset (Site (k+1)), Sparse α L F →
        (∑ ω, if (F:Set (Site (k+1))) ⊆ Z ω then μ ω else 0) ≤ p^F.card) →
      ∀ (x : Site (k+1)) (R : ℕ),
        (∑ ω, if ¬ Regular (Z ω) x R M ν then μ ω else 0) ≤
          C*((1+(R:ℝ))^(k+1)*p^(2*(k+1))+(1+(R:ℝ))^(-a)) := by
  have hbR : (1:ℝ) < b := by exact_mod_cast (show 1 < b by omega)
  obtain ⟨γ,hγ,hbγ⟩ := exists_scale_exponent hbR
  let c : ℝ := (16*(b:ℝ))^(-γ)
  have hc : 0 < c := Real.rpow_pos_of_pos (by positivity) _
  obtain ⟨C,hC,hreg⟩ := regularity_bound_of_tail k M α L ν a c γ hα hL hν ha hc hγ
  let B : ℝ := (49^(k+1)*(b^(k+1))^2:ℕ)
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨Real.exp (-2)/B,by positivity,C,hC,?_⟩
  intro Ω inst μ Z p hμ hprob hp hps htest x R
  apply hreg Ω μ Z p hμ htest _ x R
  intro z r hr
  have hL' : (1:ℝ) ≤ L := by
    have hh : (1:ℝ) ≤ (2*(k+1):ℕ) := by exact_mod_cast (show 1 ≤ 2*(k+1) by omega)
    exact hh.trans hL
  have ht := stretched_tail_of_scales μ hμ hprob Z (b:ℝ) γ hbR hγ hbγ ?_ z r hr
  · convert ht using 1
    rw [Real.div_rpow hr (by positivity)]
    dsimp [c]
    rw [Real.rpow_neg (by positivity)]
    ring_nf
  · intro n z
    calc
      _ ≤ (B*p)^(2^n) := lattice_crossing_mass_bound (k+1) b hb α L hα hL' hba μ hμ Z p hp htest n z
      _ ≤ (Real.exp (-2))^(2^n) := by
        apply pow_le_pow_left₀ (mul_nonneg hB.le hp)
        have hh := (le_div_iff₀ hB).mp hps
        simpa only [mul_comm] using hh
      _ = Real.exp (-2*(2:ℝ)^n) := by rw [←Real.exp_nat_mul]; congr 1; push_cast; ring

end Heisenberg.LatticeRegular

end

end OAI
