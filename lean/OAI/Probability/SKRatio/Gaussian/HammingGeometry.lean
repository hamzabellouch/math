import Mathlib
import OAI.Probability.SKRatio.FiniteChain.Mean
import OAI.Probability.SKRatio.Calculus.RowControl

namespace OAI

section
noncomputable section
open scoped BigOperators Topology Matrix
open MeasureTheory Filter
namespace SKRatio.Calculus
attribute [local instance] Classical.propDecidable

lemma hammingDist_real_sum {n : ℕ} (x y : Spin n) :
    (hammingDist x y : ℝ) = ∑ i, if x i = y i then 0 else 1 := by
  simp only [hammingDist,Finset.card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero,
    ite_not]

lemma hamming_exp_sum {n : ℕ} (ρ : ℝ) (y : Spin n) :
    (∑ x : Spin n, Real.exp (-ρ*(hammingDist x y:ℝ))) = (1+Real.exp (-ρ))^n := by
  have he (x : Spin n) : Real.exp (-ρ*(hammingDist x y:ℝ)) =
      ∏ i, (if x i = y i then (1:ℝ) else Real.exp (-ρ)) := by
    rw [hammingDist_real_sum,Finset.mul_sum,Real.exp_sum]
    apply Finset.prod_congr rfl
    intro i _
    split_ifs <;> simp
  simp_rw [he]
  rw [← Fintype.prod_sum (fun (i : Fin n) (b : Bool) => if b = y i then (1:ℝ) else Real.exp (-ρ))]
  have hb (i : Fin n) : (∑ b : Bool, if b = y i then (1:ℝ) else Real.exp (-ρ)) =
      1+Real.exp (-ρ) := by
    cases y i <;> simp [add_comm]
  simp only [hb,Finset.prod_const,Finset.card_univ,Fintype.card_fin]

def spinVector {n : ℕ} (x : Spin n) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun i => spinValue (x i))

lemma spinVector_norm_sq {n : ℕ} (x : Spin n) : ‖spinVector x‖^2 = (n:ℝ) := by
  simp [spinVector,EuclideanSpace.real_norm_sq_eq,Independent.spinValue_sq]

lemma spinVector_sub_norm_sq {n : ℕ} (x y : Spin n) :
    ‖spinVector x-spinVector y‖^2 = 4*(hammingDist x y:ℝ) := by
  rw [EuclideanSpace.real_norm_sq_eq,hammingDist_real_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  change (spinValue (x i)-spinValue (y i))^2 = _
  cases hx : x i <;> cases hy : y i <;> norm_num [spinValue]

lemma hamiltonian_eq_inner {n : ℕ} (g : Disorder n) (x : Spin n) :
    hamiltonian g 0 x = (1/2:ℝ)*inner ℝ (spinVector x)
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) (coupling g) (spinVector x)) := by
  rw [Matrix.inner_toEuclideanCLM (coupling g : Matrix (Fin n) (Fin n) ℝ) (spinVector x) (spinVector x)]
  simp only [hamiltonian,Pi.zero_apply,zero_mul,Finset.sum_const_zero,add_zero,dotProduct,
    Matrix.mulVec,Finset.mul_sum,spinVector,mul_assoc]

lemma abs_hamiltonian_sub_hamming {n : ℕ} (g : Disorder n) (x y : Spin n) :
    |hamiltonian g 0 x-hamiltonian g 0 y| ≤
      2*euclideanOpNorm (coupling g)*Real.sqrt n*Real.sqrt (hammingDist x y) := by
  let T := Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) (coupling g)
  have hid : hamiltonian g 0 x-hamiltonian g 0 y = (1/2:ℝ)*(
      inner ℝ (spinVector x) (T (spinVector x-spinVector y))+
      inner ℝ (spinVector x-spinVector y) (T (spinVector y))) := by
    rw [hamiltonian_eq_inner,hamiltonian_eq_inner,map_sub,inner_sub_right,inner_sub_left]
    dsimp only [T]
    ring
  have hnorm (z : Spin n) : ‖spinVector z‖ = Real.sqrt n := by
    rw [← spinVector_norm_sq z,Real.sqrt_sq (norm_nonneg _)]
  have hdiff : ‖spinVector x-spinVector y‖ = 2*Real.sqrt (hammingDist x y) := by
    rw [← Real.sqrt_sq (norm_nonneg (spinVector x-spinVector y)),spinVector_sub_norm_sq,
      Real.sqrt_mul (by norm_num : (0:ℝ)≤4)]
    norm_num
  rw [hid,abs_mul,abs_of_nonneg (by norm_num : (0:ℝ)≤1/2)]
  calc
    _ ≤ (1/2:ℝ)*(|inner ℝ (spinVector x) (T (spinVector x-spinVector y))|+
        |inner ℝ (spinVector x-spinVector y) (T (spinVector y))|) :=
      mul_le_mul_of_nonneg_left (abs_add_le _ _) (by norm_num)
    _ ≤ (1/2:ℝ)*(‖spinVector x‖*(euclideanOpNorm (coupling g)*‖spinVector x-spinVector y‖)+
        ‖spinVector x-spinVector y‖*(euclideanOpNorm (coupling g)*‖spinVector y‖)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply add_le_add
      · exact (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left
          (T.le_opNorm _) (norm_nonneg _))
      · exact (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left
          (T.le_opNorm _) (norm_nonneg _))
    _ = _ := by rw [hnorm,hnorm,hdiff]; ring

lemma mass_le_of_hamming {n : ℕ} (g : Disorder n) {K δ : ℝ}
    (hK : 0 ≤ K) (hδ : 0 ≤ δ) (hnorm : euclideanOpNorm (coupling g) ≤ K)
    (x y : Spin n) (hxy : (hammingDist x y:ℝ) ≤ δ*n) :
    mass g 0 x ≤ Real.exp (2*K*Real.sqrt δ*n)*mass g 0 y := by
  have he := abs_hamiltonian_sub_hamming g x y
  have hgeom : |hamiltonian g 0 x-hamiltonian g 0 y| ≤ 2*K*Real.sqrt δ*n := by
    calc
      _ ≤ 2*euclideanOpNorm (coupling g)*Real.sqrt n*Real.sqrt (hammingDist x y) := he
      _ ≤ 2*K*Real.sqrt n*Real.sqrt (δ*n) := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hnorm (by norm_num))
            (Real.sqrt_nonneg _)
        · exact Real.sqrt_le_sqrt hxy
        · exact Real.sqrt_nonneg _
        · positivity
      _ = (2*K*Real.sqrt δ)*(Real.sqrt n)^2 := by rw [Real.sqrt_mul hδ]; ring
      _ = _ := by rw [Real.sq_sqrt (Nat.cast_nonneg n)]
  have hh : hamiltonian g 0 x ≤ 2*K*Real.sqrt δ*n+hamiltonian g 0 y := by
    have h := (le_abs_self _).trans hgeom
    linarith only [h]
  unfold mass weight
  rw [← mul_div_assoc,← Real.exp_add]
  exact div_le_div_of_nonneg_right (Real.exp_le_exp.mpr hh) (partition_pos g 0).le

lemma hamming_ball_exp_bound {n : ℕ} (y : Spin n) {δ ρ : ℝ} (hρ : 0 ≤ ρ) :
    (∑ x : Spin n, if (hammingDist x y:ℝ) ≤ δ*n then (1:ℝ) else 0) ≤
      Real.exp ((ρ*δ+Real.log (1+Real.exp (-ρ)))*n) := by
  have hle (x : Spin n) : (if (hammingDist x y:ℝ) ≤ δ*n then (1:ℝ) else 0) ≤
      Real.exp (ρ*δ*n)*Real.exp (-ρ*(hammingDist x y:ℝ)) := by
    rw [← Real.exp_add]
    split_ifs with hx
    · apply Real.one_le_exp_iff.mpr
      nlinarith only [mul_le_mul_of_nonneg_left hx hρ]
    · exact Real.exp_nonneg _
  calc
    _ ≤ _ := Finset.sum_le_sum (fun x _ => hle x)
    _ = Real.exp (ρ*δ*n)*(1+Real.exp (-ρ))^n := by rw [← Finset.mul_sum,hamming_exp_sum]
    _ = _ := by
      rw [show (1+Real.exp (-ρ))^n = Real.exp (Real.log (1+Real.exp (-ρ))*(n:ℝ)) by
        rw [mul_comm,Real.exp_nat_mul,Real.exp_log (by positivity)],← Real.exp_add]
      congr 1
      ring

def hammingNeighborhood {n : ℕ} (B : Set (Spin n)) (δ : ℝ) : Set (Spin n) :=
  {x | ∃ y ∈ B, (hammingDist x y:ℝ) ≤ δ*n}

lemma gibbs_hamming_neighborhood {n : ℕ} (g : Disorder n) (B : Set (Spin n))
    {K κ δ ρ : ℝ} (hK : 0 ≤ K) (hδ : 0 ≤ δ) (hρ : 0 ≤ ρ)
    (hnorm : euclideanOpNorm (coupling g) ≤ K)
    (hsmall : FiniteLaw.mean (mass g 0) (fun x => if x ∈ B then 1 else 0) ≤ Real.exp (-κ*n)) :
    FiniteLaw.mean (mass g 0) (fun x => if x ∈ hammingNeighborhood B δ then 1 else 0) ≤
      Real.exp ((-κ+2*K*Real.sqrt δ+ρ*δ+Real.log (1+Real.exp (-ρ)))*n) := by
  let a := Real.exp (2*K*Real.sqrt δ*n)
  let b := Real.exp ((ρ*δ+Real.log (1+Real.exp (-ρ)))*n)
  have hpoint (x : Spin n) : mass g 0 x*(if x ∈ hammingNeighborhood B δ then 1 else 0) ≤
      ∑ y : Spin n, if y ∈ B then a*mass g 0 y*(if (hammingDist x y:ℝ) ≤ δ*n then 1 else 0) else 0 := by
    by_cases hx : x ∈ hammingNeighborhood B δ
    · simp only [hx,↓reduceIte,mul_one]
      obtain ⟨y,hy,hxy⟩ := hx
      apply (mass_le_of_hamming g hK hδ hnorm x y hxy).trans
      apply le_trans _ (Finset.single_le_sum (fun z _ => by
        have := mass_nonneg g 0 z
        dsimp only [a]; positivity) (Finset.mem_univ y))
      simp [hy,hxy,a]
    · simp only [hx,↓reduceIte,mul_zero]
      exact Finset.sum_nonneg (fun y _ => by have := mass_nonneg g 0 y; dsimp only [a]; positivity)
  calc
    _ ≤ ∑ x : Spin n, ∑ y : Spin n,
        if y ∈ B then a*mass g 0 y*(if (hammingDist x y:ℝ) ≤ δ*n then 1 else 0) else 0 :=
      Finset.sum_le_sum (fun x _ => hpoint x)
    _ = ∑ y : Spin n, if y ∈ B then a*mass g 0 y*
        (∑ x : Spin n, if (hammingDist x y:ℝ) ≤ δ*n then 1 else 0) else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro y _
      by_cases hy : y ∈ B <;> simp only [hy,↓reduceIte,Finset.mul_sum,Finset.sum_const_zero]
    _ ≤ ∑ y : Spin n, a*b*(mass g 0 y*(if y ∈ B then 1 else 0)) := by
      apply Finset.sum_le_sum
      intro y _
      by_cases hy : y ∈ B
      · simp only [hy,↓reduceIte,mul_one]
        calc
          _ ≤ a*mass g 0 y*b := mul_le_mul_of_nonneg_left (hamming_ball_exp_bound y hρ)
            (mul_nonneg (Real.exp_nonneg _) (mass_nonneg g 0 y))
          _ = _ := by ring
      · simp [hy]
    _ = a*b*FiniteLaw.mean (mass g 0) (fun y => if y ∈ B then 1 else 0) := by
      simp only [FiniteLaw.mean,Finset.mul_sum]
    _ ≤ a*b*Real.exp (-κ*n) := mul_le_mul_of_nonneg_left hsmall (by dsimp only [a,b]; positivity)
    _ = _ := by dsimp only [a,b]; rw [← Real.exp_add,← Real.exp_add]; congr 1; ring

lemma exists_small_hamming_radius {κ K : ℝ} (hκ : 0 < κ) :
    ∃ δ ρ : ℝ, 0 < δ ∧ δ < 1/2 ∧ 0 ≤ ρ ∧
      2*K*Real.sqrt δ+ρ*δ+Real.log (1+Real.exp (-ρ)) < κ/2 := by
  have he : Tendsto (fun ρ : ℝ => Real.exp (-ρ)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot
  have hl : Tendsto (fun ρ : ℝ => Real.log (1+Real.exp (-ρ))) atTop (𝓝 0) := by
    have h := ((tendsto_const_nhds.add he).log (by norm_num : (1:ℝ)+0≠0))
    simpa only [add_zero,Real.log_one] using h
  obtain ⟨ρ,hρ,hrsmall⟩ := ((eventually_ge_atTop (0:ℝ)).and
    (hl.eventually (gt_mem_nhds (by linarith : (0:ℝ)<κ/2)))).exists
  let f (δ : ℝ) := 2*K*Real.sqrt δ+ρ*δ+Real.log (1+Real.exp (-ρ))
  have hf : Continuous f := by fun_prop
  have hfs : f 0 < κ/2 := by simpa [f] using hrsmall
  obtain ⟨e,he0,hee⟩ := Metric.eventually_nhds_iff.mp
    (hf.continuousAt.tendsto.eventually (gt_mem_nhds hfs))
  let δ := min e (1/2) / 2
  have hd : 0 < δ := by dsimp only [δ]; positivity
  have hde : δ < e := by dsimp only [δ]; linarith only [min_le_left e (1/2),he0]
  have hdhalf : δ < 1/2 := by dsimp only [δ]; linarith only [min_le_right e (1/2)]
  refine ⟨δ,ρ,hd,hdhalf,hρ,?_⟩
  exact hee (by simpa only [Real.dist_eq,sub_zero,abs_of_pos hd] using hde)

def hammingTo {n : ℕ} (B : Set (Spin n)) (x : Spin n) : ℕ :=
  if h : B.Nonempty then B.toFinset.inf' (Set.toFinset_nonempty.mpr h) (hammingDist x) else 0

lemma hammingTo_attained {n : ℕ} (B : Set (Spin n)) (hB : B.Nonempty) (x : Spin n) :
    ∃ y ∈ B, hammingTo B x = hammingDist x y := by
  obtain ⟨y,hy,he⟩ := Finset.exists_mem_eq_inf' (Set.toFinset_nonempty.mpr hB) (hammingDist x)
  exact ⟨y,Set.mem_toFinset.mp hy,by simpa only [hammingTo,dite_eq_left hB] using he⟩

lemma hammingTo_le {n : ℕ} (B : Set (Spin n)) (x y : Spin n) (hy : y ∈ B) :
    hammingTo B x ≤ hammingDist x y := by
  have hB : B.Nonempty := ⟨y,hy⟩
  simp only [hammingTo,dite_eq_left hB]
  exact Finset.inf'_le _ (Set.mem_toFinset.mpr hy)

lemma hammingTo_zero_of_mem {n : ℕ} (B : Set (Spin n)) (x : Spin n) (hx : x ∈ B) :
    hammingTo B x = 0 := by
  have h := hammingTo_le B x x hx
  simpa only [hammingDist_self,Nat.le_zero] using h

lemma hammingTo_triangle {n : ℕ} (B : Set (Spin n)) (hB : B.Nonempty) (x z : Spin n) :
    hammingTo B x ≤ hammingDist x z+hammingTo B z := by
  obtain ⟨y,hy,he⟩ := hammingTo_attained B hB z
  rw [he]
  exact (hammingTo_le B x y hy).trans (hammingDist_triangle x z y)

lemma hammingTo_le_radius_iff {n : ℕ} (B : Set (Spin n)) (hB : B.Nonempty)
    (x : Spin n) (δ : ℝ) :
    (hammingTo B x:ℝ) ≤ δ*n ↔ x ∈ hammingNeighborhood B δ := by
  constructor
  · intro hx
    obtain ⟨y,hy,he⟩ := hammingTo_attained B hB x
    exact ⟨y,hy,by simpa only [he] using hx⟩
  · rintro ⟨y,hy,hxy⟩
    have hcast : (hammingTo B x:ℝ) ≤ (hammingDist x y:ℝ) := by
      exact_mod_cast hammingTo_le B x y hy
    exact hcast.trans hxy

lemma hammingDist_replace_le_one {n : ℕ} (x : Spin n) (i : Fin n) :
    hammingDist (replace x i true) (replace x i false) ≤ 1 := by
  unfold hammingDist
  apply Finset.card_le_one.mpr
  intro a ha b hb
  have h (a : Fin n) (ha : a ∈ Finset.univ.filter
      (fun a => replace x i true a ≠ replace x i false a)) : a = i := by
    by_contra hne
    exact (Finset.mem_filter.mp ha).2 (by simp [replace,Function.update_of_ne hne])
  exact (h a ha).trans (h b hb).symm

def distanceObservable {n : ℕ} (B : Set (Spin n)) : Observables n :=
  fun x => (hammingTo B x:ℝ)/Real.sqrt n

lemma distanceObservable_nonneg {n : ℕ} (B : Set (Spin n)) (x : Spin n) :
    0 ≤ distanceObservable B x := by unfold distanceObservable; positivity

lemma distanceObservable_zero {n : ℕ} (B : Set (Spin n)) (x : Spin n) (hx : x ∈ B) :
    distanceObservable B x = 0 := by simp [distanceObservable,hammingTo_zero_of_mem B x hx]

lemma unweightedGradient_distanceObservable {n : ℕ} (hn : 0 < n)
    (B : Set (Spin n)) (hB : B.Nonempty) (x : Spin n) :
    unweightedGradient (distanceObservable B) x ≤ 1/4 := by
  have hsq : (Real.sqrt n)^2 = (n:ℝ) := Real.sq_sqrt (Nat.cast_nonneg n)
  have hspos : 0 < Real.sqrt n := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)
  have hdiff (i : Fin n) : |(hammingTo B (replace x i true):ℝ)-hammingTo B (replace x i false)| ≤ 1 := by
    apply abs_le.mpr
    have h1 := hammingTo_triangle B hB (replace x i true) (replace x i false)
    have h2 := hammingTo_triangle B hB (replace x i false) (replace x i true)
    rw [hammingDist_comm (replace x i false)] at h2
    have hd := hammingDist_replace_le_one x i
    have h1r : (hammingTo B (replace x i true):ℝ) ≤
        (hammingDist (replace x i true) (replace x i false):ℝ)+hammingTo B (replace x i false) := by
      exact_mod_cast h1
    have h2r : (hammingTo B (replace x i false):ℝ) ≤
        (hammingDist (replace x i true) (replace x i false):ℝ)+hammingTo B (replace x i true) := by
      exact_mod_cast h2
    have hdr : (hammingDist (replace x i true) (replace x i false):ℝ) ≤ 1 := by
      exact_mod_cast hd
    constructor <;> linarith only [h1r,h2r,hdr]
  calc
    _ ≤ ∑ _i : Fin n, (1/(2*Real.sqrt n))^2 := by
      apply Finset.sum_le_sum
      intro i _
      have h := (sq_le_sq₀ (abs_nonneg _) (by norm_num)).mpr (hdiff i)
      rw [sq_abs] at h
      unfold halfDiff distanceObservable
      have he : (((hammingTo B (replace x i true):ℝ)/Real.sqrt n-
          (hammingTo B (replace x i false):ℝ)/Real.sqrt n)/2)^2 =
          (((hammingTo B (replace x i true):ℝ)-(hammingTo B (replace x i false):ℝ))^2)*
            (1/(2*Real.sqrt n))^2 := by ring
      rw [he]
      simpa only [one_mul,one_pow] using mul_le_mul_of_nonneg_right h (sq_nonneg (1/(2*Real.sqrt n)))
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      field_simp
      nlinarith only [hsq]

lemma distanceObservable_mean_lower {n : ℕ} (hn : 0 < n) (B : Set (Spin n))
    (hB : B.Nonempty) (p : Spin n → ℝ) (hp : ∀ y, 0 ≤ p y) (hp1 : ∑ y, p y = 1)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hhalf : FiniteLaw.mean p (fun y => if y ∈ hammingNeighborhood B δ then 1 else 0) ≤ 1/2) :
    δ*Real.sqrt n/2 ≤ FiniteLaw.mean p (distanceObservable B) := by
  have hspos : 0 < Real.sqrt n := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)
  have hdist (y : Spin n) : δ*Real.sqrt n*(1-(if y ∈ hammingNeighborhood B δ then 1 else 0)) ≤
      distanceObservable B y := by
    by_cases hy : y ∈ hammingNeighborhood B δ
    · simp only [hy,↓reduceIte,sub_self,mul_zero]
      exact distanceObservable_nonneg B y
    · have hgt := lt_of_not_ge (mt (hammingTo_le_radius_iff B hB y δ).mp hy)
      simp only [hy,↓reduceIte,sub_zero,mul_one]
      rw [distanceObservable,le_div_iff₀ hspos]
      calc
        _ = δ*(n:ℝ) := by rw [mul_assoc,← pow_two,Real.sq_sqrt (Nat.cast_nonneg n)]
        _ ≤ _ := hgt.le
  have hs := Finset.sum_le_sum (s := Finset.univ)
    (fun y _ => mul_le_mul_of_nonneg_left (hdist y) (hp y))
  have hsum : (∑ y, p y*(δ*Real.sqrt n*(1-(if y ∈ hammingNeighborhood B δ then 1 else 0)))) =
      δ*Real.sqrt n*(1-FiniteLaw.mean p (fun y => if y ∈ hammingNeighborhood B δ then 1 else 0)) := by
    simp only [FiniteLaw.mean,Finset.mul_sum,mul_sub,mul_one,Finset.sum_sub_distrib]
    rw [show (∑ y, p y*(δ*Real.sqrt n)) = δ*Real.sqrt n by rw [← Finset.sum_mul,hp1,one_mul]]
    congr 1
    apply Finset.sum_congr rfl
    intro y _
    ring
  rw [hsum] at hs
  have hm := mul_le_mul_of_nonneg_left hhalf (mul_nonneg hδ (Real.sqrt_nonneg n))
  dsimp only [FiniteLaw.mean] at *
  linarith only [hs,hm]

end SKRatio.Calculus

end
end

end OAI
