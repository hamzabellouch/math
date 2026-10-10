import OAI.MathematicalPhysics.Heisenberg.FlowCongestion

namespace OAI

noncomputable section

open scoped Classical
open scoped Classical
open Filter Topology
open scoped Classical
open scoped Classical
open Module
open scoped Classical
open scoped Classical BigOperators

open scoped Classical BigOperators
namespace Heisenberg.SparseSum

lemma dyadic_power (r : ℝ) (n : ℕ) : ((2:ℝ)^n)^r = ((2:ℝ)^r)^n := by
  rw [←Real.rpow_natCast,←Real.rpow_mul (by norm_num),mul_comm,
    Real.rpow_mul (by norm_num),Real.rpow_natCast]

theorem sparse_kernel_sum {I V : Type*} [Fintype I] [PseudoMetricSpace V]
    (x : I → V) (z : V) (α q L : ℝ) (hα : 0 ≤ α) (hαq : α < q) (hL : 0 ≤ L)
    (hgrowth : ∀ r : ℝ, 0 ≤ r →
      ((Finset.univ.filter (fun i => dist (x i) z ≤ r)).card:ℝ) ≤ L*(1+r)^α) :
    (∑ i, (1+dist (x i) z)^(-q)) ≤
      (2:ℝ)^q * (L*(2:ℝ)^α) * (1-(2:ℝ)^(α-q))⁻¹ := by
  have hq : 0 < q := lt_of_le_of_lt hα hαq
  let a : ℝ := (2:ℝ)^(-q)
  have ha0 : 0 ≤ a := by dsimp [a]; positivity
  have ha1 : a < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hs : Summable (fun n : ℕ => a^n) := (hasSum_geometric_of_lt_one ha0 ha1).summable
  let F : I → ℕ → ℝ := fun i n => if dist (x i) z ≤ (2:ℝ)^n then a^n else 0
  have hF : ∀ i n, 0 ≤ F i n := by intro i n; dsimp [F]; split_ifs <;> positivity
  have hsF : ∀ i, Summable (F i) := by
    intro i
    exact Summable.of_nonneg_of_le (hF i) (fun n => by dsimp [F]; split_ifs <;> simp [pow_nonneg ha0]) hs
  have hbound : ∀ i, (1+dist (x i) z)^(-q) ≤ (2:ℝ)^q*(∑' n, F i n) := by
    intro i
    obtain ⟨n,hn,hn'⟩ := exists_nat_pow_near
      (show 1 ≤ 1+dist (x i) z by linarith [dist_nonneg (x:=x i) (y:=z)]) (by norm_num : (1:ℝ) < 2)
    have hd : dist (x i) z ≤ (2:ℝ)^(n+1) := by linarith
    have hp : (1+dist (x i) z)^(-q) ≤ ((2:ℝ)^n)^(-q) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hn (by linarith)
    rw [dyadic_power] at hp
    have hprod : (2:ℝ)^q*a=1 := by dsimp [a]; rw [←Real.rpow_add (by norm_num)]; simp
    have he : ((2:ℝ)^(-q))^n = (2:ℝ)^q*a^(n+1) := by
      rw [pow_succ]
      calc
        _ = 1*a^n := by simp [a]
        _ = _ := by rw [←hprod]; ring
    rw [he] at hp
    apply hp.trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have hh := (hsF i).le_tsum (n+1) (fun j _ => hF i j)
    simpa only [F,ite_eq_left hd] using hh
  let b : ℝ := (2:ℝ)^(α-q)
  have hb0 : 0 ≤ b := by dsimp [b]; positivity
  have hb1 : b < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hsb : Summable (fun n : ℕ => L*(2:ℝ)^α*b^n) :=
    (hasSum_geometric_of_lt_one hb0 hb1).summable.mul_left _
  have hc : ∀ n, (∑ i, F i n) ≤ L*(2:ℝ)^α*b^n := by
    intro n
    have hcount := hgrowth ((2:ℝ)^n) (by positivity)
    have ht : 1+(2:ℝ)^n ≤ 2*(2:ℝ)^n := by linarith [one_le_pow₀ (n:=n) (by norm_num : (1:ℝ) ≤ 2)]
    have hp := Real.rpow_le_rpow (by positivity) ht hα
    rw [Real.mul_rpow (by norm_num) (by positivity),dyadic_power] at hp
    calc
      _ = ((Finset.univ.filter (fun i => dist (x i) z ≤ (2:ℝ)^n)).card:ℝ)*a^n := by
        simp [F,←Finset.sum_filter]
      _ ≤ (L*(1+(2:ℝ)^n)^α)*a^n := mul_le_mul_of_nonneg_right hcount (pow_nonneg ha0 _)
      _ ≤ (L*((2:ℝ)^α*((2:ℝ)^α)^n))*a^n := by gcongr
      _ = _ := by
        have hab : (2:ℝ)^α*a=b := by dsimp [a,b]; rw [←Real.rpow_add (by norm_num)]; congr 1
        rw [show (L*((2:ℝ)^α*((2:ℝ)^α)^n))*a^n = L*(2:ℝ)^α*(((2:ℝ)^α)^n*a^n) by ring,
          ←mul_pow,hab]
  calc
    _ ≤ ∑ i, (2:ℝ)^q*(∑' n, F i n) := Finset.sum_le_sum (fun i _ => hbound i)
    _ = (2:ℝ)^q*(∑' n, ∑ i, F i n) := by
      rw [←Finset.mul_sum,←Summable.tsum_finsetSum (fun i _ => hsF i)]
    _ ≤ (2:ℝ)^q*(∑' n, L*(2:ℝ)^α*b^n) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact (summable_sum (fun i _ => hsF i)).tsum_le_tsum hc hsb
    _ = _ := by rw [tsum_mul_left,tsum_geometric_of_lt_one hb0 hb1]; dsimp [b]; ring

end Heisenberg.SparseSum

namespace Heisenberg.FlowAggregation

theorem total_energy {I E V : Type*} [Fintype I] [PseudoMetricSpace V]
    (x : I → V) (J : I → E → ℝ) (α q L B : ℝ)
    (hα : 0 ≤ α) (hαq : α < q) (hL : 0 ≤ L) (hB : 0 ≤ B)
    (hgrowth : ∀ z r, 0 ≤ r →
      ((Finset.univ.filter (fun i => dist (x i) z ≤ r)).card:ℝ) ≤ L*(1+r)^α)
    (hs : ∀ i j, Summable (fun e => |J i e*J j e|))
    (hoverlap : ∀ i j, (∑' e, |J i e*J j e|) ≤ B*(1+dist (x i) (x j))^(-q)) :
    Summable (fun e => (∑ i, J i e)^2) ∧
    (∑' e, (∑ i, J i e)^2) ≤
      (B*((2:ℝ)^q*(L*(2:ℝ)^α)*(1-(2:ℝ)^(α-q))⁻¹))*(Fintype.card I) := by
  let F : E → ℝ := fun e => ∑ i, ∑ j, |J i e*J j e|
  have hF : Summable F := summable_sum (fun i _ => summable_sum (fun j _ => hs i j))
  have hbound : ∀ e, (∑ i, J i e)^2 ≤ F e := by
    intro e
    calc
      _ = ∑ i, ∑ j, J i e*J j e := by rw [sq,Finset.sum_mul]; simp only [Finset.mul_sum]
      _ ≤ _ := Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => le_abs_self _))
  have hsquare := Summable.of_nonneg_of_le (fun e => sq_nonneg _) hbound hF
  refine ⟨hsquare,?_⟩
  calc
    _ ≤ ∑' e, F e := hsquare.tsum_le_tsum hbound hF
    _ = ∑ i, ∑ j, ∑' e, |J i e*J j e| := by
      rw [Summable.tsum_finsetSum (fun i _ => summable_sum (fun j _ => hs i j))]
      apply Finset.sum_congr rfl
      intro i _
      exact Summable.tsum_finsetSum (fun j _ => hs i j)
    _ ≤ ∑ i, ∑ j, B*(1+dist (x i) (x j))^(-q) :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hoverlap i j))
    _ ≤ ∑ _i : I, B*((2:ℝ)^q*(L*(2:ℝ)^α)*(1-(2:ℝ)^(α-q))⁻¹) := by
      apply Finset.sum_le_sum
      intro i _
      rw [←Finset.mul_sum]
      apply mul_le_mul_of_nonneg_left _ hB
      simpa only [dist_comm (x i)] using
        Heisenberg.SparseSum.sparse_kernel_sum x (x i) α q L hα hαq hL (hgrowth (x i))
    _ = _ := by simp [mul_comm]

lemma kernel_displacement {V : Type*} [PseudoMetricSpace V]
    (x x' y y' : V) (R q : ℝ) (_hR : 0 ≤ R) (hq : 0 ≤ q)
    (hy : dist y x ≤ R) (hy' : dist y' x' ≤ R) :
    (1+dist y y')^(-q) ≤ if dist x x' ≤ 4*R then 1 else
      (2:ℝ)^q*(1+dist x x')^(-q) := by
  split_ifs with hn
  · exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith [dist_nonneg (x:=y) (y:=y')]) (by linarith)
  · have ht : dist x x' ≤ 2*R+dist y y' := by
      have h := dist_triangle4 x y y' x'
      rw [dist_comm x y] at h
      linarith
    have hbase : 1+dist x x' ≤ 2*(1+dist y y') := by linarith [lt_of_not_ge hn]
    have hp := Real.rpow_le_rpow_of_nonpos (by positivity : (0:ℝ) < 1+dist x x') hbase (show -q ≤ 0 by linarith)
    rw [Real.mul_rpow (by norm_num) (by positivity)] at hp
    have hc : (2:ℝ)^q*(2:ℝ)^(-q)=1 := by rw [←Real.rpow_add (by norm_num)]; simp
    have hh := mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 2) q)
    simpa only [←mul_assoc,hc,one_mul] using hh

lemma averaged_overlap {A B E : Type*} [Fintype A] [Fintype B]
    (μ : A → ℝ) (ν : B → ℝ) (J : A → E → ℝ) (K : B → E → ℝ) (C : ℝ)
    (hμ : ∀ a, 0 ≤ μ a) (hν : ∀ b, 0 ≤ ν b)
    (hm : ∑ a, μ a ≤ 1) (hn : ∑ b, ν b ≤ 1) (hC : 0 ≤ C)
    (hs : ∀ a b, Summable (fun e => |J a e*K b e|))
    (hb : ∀ a b, μ a ≠ 0 → ν b ≠ 0 → (∑' e, |J a e*K b e|) ≤ C) :
    Summable (fun e => |(∑ a, μ a*J a e)*(∑ b, ν b*K b e)|) ∧
    (∑' e, |(∑ a, μ a*J a e)*(∑ b, ν b*K b e)|) ≤ C := by
  let F : E → ℝ := fun e => ∑ a, ∑ b, (μ a*ν b)*|J a e*K b e|
  have hsF : Summable F := summable_sum (fun a _ => summable_sum (fun b _ => (hs a b).mul_left _))
  have hle : ∀ e, |(∑ a, μ a*J a e)*(∑ b, ν b*K b e)| ≤ F e := by
    intro e
    calc
      _ = |∑ a, ∑ b, (μ a*ν b)*(J a e*K b e)| := by
        congr 1
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro a _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro b _
        ring
      _ ≤ ∑ a, |∑ b, (μ a*ν b)*(J a e*K b e)| := Finset.abs_sum_le_sum_abs ..
      _ ≤ F e := by
        apply Finset.sum_le_sum
        intro a _
        simpa only [abs_mul,abs_of_nonneg (hμ a),abs_of_nonneg (hν _)] using
          (Finset.abs_sum_le_sum_abs (s:=Finset.univ) (f:=fun b => (μ a*ν b)*(J a e*K b e)))
  have hsres := Summable.of_nonneg_of_le (fun e => abs_nonneg _) hle hsF
  refine ⟨hsres,?_⟩
  calc
    _ ≤ ∑' e, F e := hsres.tsum_le_tsum hle hsF
    _ = ∑ a, ∑ b, (μ a*ν b)*(∑' e, |J a e*K b e|) := by
      rw [Summable.tsum_finsetSum (fun a _ => summable_sum (fun b _ => (hs a b).mul_left _))]
      apply Finset.sum_congr rfl
      intro a _
      rw [Summable.tsum_finsetSum (fun b _ => (hs a b).mul_left _)]
      simp only [tsum_mul_left]
    _ ≤ ∑ a, ∑ b, (μ a*ν b)*C := by
      apply Finset.sum_le_sum
      intro a _
      apply Finset.sum_le_sum
      intro b _
      by_cases ha : μ a = 0
      · simp [ha]
      by_cases hb' : ν b = 0
      · simp [hb']
      exact mul_le_mul_of_nonneg_left (hb a b ha hb') (mul_nonneg (hμ a) (hν b))
    _ = (∑ a, μ a)*(∑ b, ν b)*C := by
      simp only [Finset.sum_mul,Finset.mul_sum]
      exact Finset.sum_comm
    _ ≤ C := by
      have hprod : (∑ a, μ a)*(∑ b, ν b) ≤ 1 := by
        exact (mul_le_mul hm hn (Finset.sum_nonneg (fun b _ => hν b)) (by norm_num)).trans_eq (by norm_num)
      simpa using mul_le_mul_of_nonneg_right hprod hC

lemma energy_le_row {I E : Type*} [Fintype I] (J : I → E → ℝ)
    (K : I → I → ℝ) (C : ℝ)
    (hs : ∀ i j, Summable (fun e => |J i e*J j e|))
    (hK : ∀ i j, (∑' e, |J i e*J j e|) ≤ K i j)
    (hrow : ∀ i, (∑ j, K i j) ≤ C) :
    Summable (fun e => (∑ i, J i e)^2) ∧
    (∑' e, (∑ i, J i e)^2) ≤ C*(Fintype.card I) := by
  let F : E → ℝ := fun e => ∑ i, ∑ j, |J i e*J j e|
  have hsF : Summable F := summable_sum (fun i _ => summable_sum (fun j _ => hs i j))
  have hb : ∀ e, (∑ i, J i e)^2 ≤ F e := by
    intro e
    calc
      _ = ∑ i, ∑ j, J i e*J j e := by rw [sq,Finset.sum_mul]; simp only [Finset.mul_sum]
      _ ≤ _ := Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => le_abs_self _))
  have hsquare := Summable.of_nonneg_of_le (fun e => sq_nonneg _) hb hsF
  refine ⟨hsquare,?_⟩
  calc
    _ ≤ ∑' e, F e := hsquare.tsum_le_tsum hb hsF
    _ = ∑ i, ∑ j, ∑' e, |J i e*J j e| := by
      rw [Summable.tsum_finsetSum (fun i _ => summable_sum (fun j _ => hs i j))]
      apply Finset.sum_congr rfl
      intro i _
      exact Summable.tsum_finsetSum (fun j _ => hs i j)
    _ ≤ ∑ i, ∑ j, K i j := Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hK i j))
    _ ≤ ∑ _i : I, C := Finset.sum_le_sum (fun i _ => hrow i)
    _ = _ := by simp [mul_comm]

theorem injection_energy {I A E V : Type*} [Fintype I] [Fintype A] [PseudoMetricSpace V]
    (x : I → V) (y : I → A → V) (μ : I → A → ℝ) (J : I → A → E → ℝ)
    (α q L B : ℝ) (hα : 0 ≤ α) (hαq : α < q) (hL : 0 ≤ L) (hB : 0 ≤ B)
    (hgrowth : ∀ z r, 0 ≤ r →
      ((Finset.univ.filter (fun i => dist (x i) z ≤ r)).card:ℝ) ≤ L*(1+r)^α)
    (hμ : ∀ i a, 0 ≤ μ i a) (hmass : ∀ i, ∑ a, μ i a ≤ 1)
    (hs : ∀ i a j b, Summable (fun e => |J i a e*J j b e|))
    (hoverlap : ∀ i a j b, (∑' e, |J i a e*J j b e|) ≤ B*(1+dist (y i a) (y j b))^(-q))
    (R : ℝ) (hR : 0 ≤ R) (hloc : ∀ i a, μ i a ≠ 0 → dist (y i a) (x i) ≤ R) :
    Summable (fun e => (∑ i, ∑ a, μ i a*J i a e)^2) ∧
    (∑' e, (∑ i, ∑ a, μ i a*J i a e)^2) ≤
      B*(L*(4:ℝ)^α + (2:ℝ)^q*((2:ℝ)^q*(L*(2:ℝ)^α)*(1-(2:ℝ)^(α-q))⁻¹)) *
        (1+R)^α*(Fintype.card I) := by
  let K : I → I → ℝ := fun i j => B*((if dist (x i) (x j) ≤ 4*R then 1 else 0) +
    (2:ℝ)^q*(1+dist (x i) (x j))^(-q))
  have hK : ∀ i j, 0 ≤ K i j := by intro i j; dsimp [K]; split_ifs <;> positivity
  have hover : ∀ i j, Summable (fun e => |(∑ a, μ i a*J i a e)*(∑ b, μ j b*J j b e)|) ∧
      (∑' e, |(∑ a, μ i a*J i a e)*(∑ b, μ j b*J j b e)|) ≤ K i j := by
    intro i j
    apply averaged_overlap (μ i) (μ j) (J i) (J j) (K i j) (hμ i) (hμ j) (hmass i) (hmass j) (hK i j) (hs i · j ·)
    intro a b ha hb
    apply (hoverlap i a j b).trans
    apply mul_le_mul_of_nonneg_left _ hB
    have hh := kernel_displacement (x i) (x j) (y i a) (y j b) R q hR (by linarith) (hloc i a ha) (hloc j b hb)
    have hp : 0 ≤ (2:ℝ)^q*(1+dist (x i) (x j))^(-q) := by positivity
    split_ifs at hh ⊢ <;> linarith
  apply energy_le_row (fun i e => ∑ a, μ i a*J i a e) K _ (fun i j => (hover i j).1) (fun i j => (hover i j).2)
  intro i
  have hcount := hgrowth (x i) (4*R) (by positivity)
  have hsum := Heisenberg.SparseSum.sparse_kernel_sum x (x i) α q L hα hαq hL (hgrowth (x i))
  have hrpow : (1+4*R)^α ≤ (4:ℝ)^α*(1+R)^α := by
    calc
      _ ≤ (4*(1+R))^α := Real.rpow_le_rpow (by positivity) (by linarith) hα
      _ = _ := Real.mul_rpow (by norm_num) (by positivity)
  have hunit : 1 ≤ (1+R)^α := Real.one_le_rpow (by linarith) hα
  have hSS : 0 ≤ (2:ℝ)^q*(L*(2:ℝ)^α)*(1-(2:ℝ)^(α-q))⁻¹ := by
    have hh : (2:ℝ)^(α-q) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
    positivity
  have he : (∑ j, K i j) = B*((Finset.univ.filter (fun j => dist (x j) (x i) ≤ 4*R)).card +
      (2:ℝ)^q*(∑ j, (1+dist (x j) (x i))^(-q))) := by
    simp only [K,←Finset.mul_sum,Finset.sum_add_distrib]
    simp [dist_comm]
  rw [he,mul_assoc]
  apply mul_le_mul_of_nonneg_left _ hB
  nlinarith [mul_le_mul_of_nonneg_left hsum (Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 2) q),
    mul_le_mul_of_nonneg_left hrpow hL,
    mul_nonneg (mul_nonneg (Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 2) q) hSS) (sub_nonneg.mpr hunit)]

end Heisenberg.FlowAggregation

end

end OAI
