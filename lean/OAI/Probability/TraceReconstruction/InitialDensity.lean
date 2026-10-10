import OAI.Probability.TraceReconstruction.Ranks

namespace OAI

/-!
# InitialDensity

Defect monomials, orthogonality, normalized initial densities, and common mass.
-/

open scoped ENNReal
noncomputable section

open Filter
open scoped Topology

noncomputable section
namespace TraceReconstruction
open FiniteLaw

/-- A monotone tuple of defect slots is uniquely identified by the
retained ranks whenever all these ranks carry defects. -/
theorem exists_unique_defect_tuple {n l u r : ℕ}
    (d : Fin u → Fin n) (hd : StrictMono d) (v : IncreasingTuple l r)
    (S : FixedSubset (Fin n) l)
    (h : ∀ i, slotAtRank S (v.val i) ∈ Set.range d) :
    ∃! j : IncreasingTuple u r, taggedRankEvent (d ∘ j.val) v.val S := by
  classical
  choose j hj using h
  have hm : StrictMono j := by
    intro a b hab
    apply hd.lt_iff_lt.mp
    rw [hj a,hj b]
    exact slotAtRank_strictMono S (v.property hab)
  refine ⟨⟨j,hm⟩,?_,?_⟩
  · intro i
    exact (hj i).symm
  · intro k hk
    apply Subtype.ext
    funext i
    apply hd.injective
    exact (hk i).symm.trans (hj i).symm

/-- The degree coefficient is the sum over actual tagged defect tuples,
not a separately postulated kernel array. -/
theorem defect_tuple_indicator {n l u r : ℕ}
    (d : Fin u → Fin n) (hd : StrictMono d) (v : IncreasingTuple l r)
    (S : FixedSubset (Fin n) l) :
    (if ∀ i, slotAtRank S (v.val i) ∈ Set.range d then (1:ℝ) else 0) =
      ∑ j : IncreasingTuple u r, if taggedRankEvent (d ∘ j.val) v.val S then 1 else 0 := by
  classical
  by_cases h : ∀ i, slotAtRank S (v.val i) ∈ Set.range d
  · obtain ⟨j,hj,hu⟩ := exists_unique_defect_tuple d hd v S h
    rw [ite_eq_left h]
    symm
    rw [Finset.sum_eq_single j]
    · exact ite_eq_left hj
    · intro k _ hkj
      have hk : ¬taggedRankEvent (d ∘ k.val) v.val S := by
        intro hk
        exact hkj (hu k hk)
      exact ite_eq_right hk
    · simp
  · rw [ite_eq_right h]
    symm
    apply Finset.sum_eq_zero
    intro j _
    apply ite_eq_right
    intro hj
    apply h
    intro i
    exact ⟨j.val i,(hj i).symm⟩

def rankDefectCoefficient {n l u r : ℕ} (hl : l ≤ n) (d : Fin u → Fin n)
    (v : IncreasingTuple l r) : ℝ := by
  classical
  exact (uniformSubsetLaw l (by simpa using hl)).expect (fun S =>
    if ∀ i, slotAtRank S (v.val i) ∈ Set.range d then 1 else 0)

theorem rankDefectCoefficient_eq {n l u r : ℕ} (hl : l ≤ n)
    (d : Fin u → Fin n) (hd : StrictMono d) (v : IncreasingTuple l r) :
    rankDefectCoefficient hl d v =
      ∑ j : IncreasingTuple u r, subsetRankKernel hl (d ∘ j.val) v.val := by
  classical
  unfold rankDefectCoefficient FiniteLaw.expect subsetRankKernel
  simp_rw [defect_tuple_indicator d hd v, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro S _
  split_ifs <;> simp

/-- Bool-mask form of the selected-rank coefficient, in the exact
multilinear density expansion. -/
theorem selected_defect_coefficient {n l : ℕ} (D : Finset (Fin n))
    (S : FixedSubset (Fin n) l) (σ : Fin l → Bool) :
    selectionCoefficient (defectAtRank D S) σ =
      if ∀ i, σ i = true → slotAtRank S i ∈ D then (1:ℝ) else 0 := by
  classical
  unfold selectionCoefficient defectAtRank
  by_cases h : ∀ i, σ i = true → slotAtRank S i ∈ D
  · rw [ite_eq_left h]
    apply Finset.prod_eq_one
    intro i _
    cases hs : σ i
    · simp
    · simp [h i hs]
  · rw [ite_eq_right h]
    push Not at h
    obtain ⟨i,hi,hni⟩ := h
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [hi,hni]

def rankMask {l r : ℕ} (v : IncreasingTuple l r) : Fin l → Bool :=
  fun i => decide (i ∈ Set.range v.val)

theorem averaged_rank_coefficient {n l u r : ℕ} (hl : l ≤ n)
    (d : Fin u → Fin n) (v : IncreasingTuple l r) :
    averagedCoefficient (uniformSubsetLaw l (by simpa using hl))
      (defectAtRank (Finset.univ.image d)) (rankMask v) =
      rankDefectCoefficient hl d v := by
  classical
  unfold averagedCoefficient rankDefectCoefficient FiniteLaw.expect
  apply Finset.sum_congr rfl
  intro S _
  congr 1
  dsimp only
  rw [selected_defect_coefficient]
  congr 1
  simp only [rankMask,decide_eq_true_eq,Finset.mem_image,Finset.mem_univ,true_and,
    Set.mem_range]
  apply propext
  constructor
  · intro h i
    exact h (v.val i) ⟨i,rfl⟩
  · rintro h i ⟨j,rfl⟩
    exact h j

end TraceReconstruction

namespace TraceReconstruction
open FiniteLaw

/-- Canonical increasing tuple associated with a selected set of ranks. -/
def tupleOfMask {l r : ℕ} (σ : Fin l → Bool) (hσ : monomialDegree σ = r) :
    IncreasingTuple l r := by
  classical
  let S : Finset (Fin l) := Finset.univ.filter (fun i => σ i = true)
  have hS : S.card = r := hσ
  exact ⟨fun i => ((S.orderIsoOfFin hS) i).val, (S.orderIsoOfFin hS).strictMono⟩

theorem rankMask_tupleOfMask {l r : ℕ} (σ : Fin l → Bool) (hσ : monomialDegree σ = r) :
    rankMask (tupleOfMask σ hσ) = σ := by
  classical
  funext i
  have he : i ∈ Set.range (tupleOfMask σ hσ).val ↔ σ i = true := by
    constructor
    · rintro ⟨j,rfl⟩
      exact (Finset.mem_filter.mp (((Finset.univ.filter (fun k => σ k = true)).orderIsoOfFin hσ) j).property).2
    · intro hi
      let z : ↥(Finset.univ.filter (fun k => σ k = true)) := ⟨i,by simp [hi]⟩
      refine ⟨((Finset.univ.filter (fun k => σ k = true)).orderIsoOfFin hσ).symm z,?_⟩
      exact congrArg Subtype.val (((Finset.univ.filter (fun k => σ k = true)).orderIsoOfFin hσ).apply_symm_apply z)
  simp only [rankMask,he]
  exact Bool.decide_eq_true

theorem tupleOfMask_injective {l r : ℕ} : Function.Injective
    (fun σ : {σ : Fin l → Bool // monomialDegree σ = r} => tupleOfMask σ.val σ.property) := by
  intro σ τ h
  apply Subtype.ext
  have he := congrArg rankMask h
  simpa only [rankMask_tupleOfMask] using he

/-- Changing from Boolean monomial labels to ordered rank tuples loses no
mass; an injection suffices for the upper bounds. -/
theorem sum_degree_coeff_sq_le {l r : ℕ} (A : (Fin l → Bool) → ℝ) :
    (∑ σ : Fin l → Bool, if monomialDegree σ = r then A σ ^ 2 else 0) ≤
      ∑ v : IncreasingTuple l r, A (rankMask v)^2 := by
  classical
  rw [← Finset.sum_filter]
  have he : (∑ σ ∈ Finset.univ.filter (fun σ : Fin l → Bool => monomialDegree σ = r), A σ ^ 2) =
      ∑ σ : {σ : Fin l → Bool // monomialDegree σ = r}, A σ.val ^ 2 := by
    exact Finset.sum_subtype _ (by intro σ; simp) _
  rw [he]
  have h := sum_injective_profile_le
    (fun σ : {σ : Fin l → Bool // monomialDegree σ = r} => tupleOfMask σ.val σ.property)
    tupleOfMask_injective (fun _ => True) (fun _ => True.intro)
    (fun v => A (rankMask v)^2) (fun _ => sq_nonneg _)
  simpa only [rankMask_tupleOfMask,ite_true] using h

end TraceReconstruction

noncomputable section
namespace TraceReconstruction
open FiniteLaw

/-- Exact orthogonality of the multilinear expansion; this avoids any
loss in the channel power in consecutive-run overlap. -/
theorem multilinear_second_moment {α : Type*} [Fintype α] (P : FiniteLaw α)
    (Z : α → ℝ) (hcenter : P.expect Z = 0) (R : ℝ)
    (hvar : P.expect (fun a => Z a^2) = R^2) (n : ℕ)
    (A : (Fin n → Bool) → ℝ) :
    (P.product n).expect (fun x => multilinear A Z x ^ 2) =
      multilinearEnergy A R := by
  induction n with
  | zero => simp [FiniteLaw.expect,FiniteLaw.product,multilinear,multilinearEnergy]
  | succ n ih =>
    rw [product_succ_expect_tail]
    simp_rw [multilinear_cons]
    have he (x : Fin n → α) :
        P.expect (fun a => (multilinear (fun σ => A (Fin.cons false σ)) Z x +
            Z a * multilinear (fun σ => A (Fin.cons true σ)) Z x)^2) =
          multilinear (fun σ => A (Fin.cons false σ)) Z x ^ 2 +
            R^2 * multilinear (fun σ => A (Fin.cons true σ)) Z x ^ 2 := by
      have hp (a : α) :
          P.mass a * (multilinear (fun σ => A (Fin.cons false σ)) Z x +
            Z a * multilinear (fun σ => A (Fin.cons true σ)) Z x)^2 =
          P.mass a * (multilinear (fun σ => A (Fin.cons false σ)) Z x)^2 +
            2 * multilinear (fun σ => A (Fin.cons false σ)) Z x *
              multilinear (fun σ => A (Fin.cons true σ)) Z x * (P.mass a * Z a) +
            (multilinear (fun σ => A (Fin.cons true σ)) Z x)^2 * (P.mass a * Z a^2) := by ring
      unfold FiniteLaw.expect
      simp_rw [hp,Finset.sum_add_distrib,← Finset.sum_mul,← Finset.mul_sum]
      simp only [FiniteLaw.expect] at hcenter hvar
      rw [P.total,hcenter,hvar]
      ring
    simp_rw [he]
    rw [multilinearEnergy_cons]
    have hadd (f g : (Fin n → α) → ℝ) :
        (P.product n).expect (fun x => f x + R^2*g x) =
          (P.product n).expect f + R^2*(P.product n).expect g := by
      unfold FiniteLaw.expect
      simp_rw [mul_add,Finset.sum_add_distrib]
      rw [Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro x _
      ring
    rw [hadd,ih,ih]

/-- Association requires only a total preorder, allowing tied likelihoods. -/
theorem FiniteLaw.associated_totalPreorder {α : Type*} [Fintype α] [Preorder α]
    (P : FiniteLaw α) (htotal : ∀ a b : α, a ≤ b ∨ b ≤ a) : P.Associated := by
  intro f g hf hg
  have hn (a b : α) : 0 ≤ (f a - f b) * (g a - g b) := by
    rcases htotal a b with hab | hba
    · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr (hf hab))
        (sub_nonpos.mpr (hg hab))
    · exact mul_nonneg (sub_nonneg.mpr (hf hba)) (sub_nonneg.mpr (hg hba))
  have h := Finset.sum_nonneg (s := Finset.univ) (fun a _ =>
    Finset.sum_nonneg (s := Finset.univ) (fun b _ => mul_nonneg (mul_nonneg (P.nonneg a)
      (P.nonneg b)) (hn a b)))
  have hid : (∑ a, ∑ b, P.mass a * P.mass b * ((f a - f b) * (g a - g b))) =
      2 * (P.expect (fun a => f a * g a) - P.expect f * P.expect g) := by
    have hp (a b : α) : P.mass a * P.mass b * ((f a - f b) * (g a - g b)) =
        (P.mass a * (f a * g a)) * P.mass b + P.mass a * (P.mass b * (f b * g b)) -
        (P.mass a * f a) * (P.mass b * g b) - (P.mass a * g a) * (P.mass b * f b) := by ring
    simp_rw [hp, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.sum_mul, P.total, one_mul, mul_one]
    unfold FiniteLaw.expect
    ring
  rw [hid] at h
  linarith

/-- Conditional average densities are nonnegative when the coordinate
likelihoods are nonnegative. -/
theorem averagedDensity_nonneg {α Ω : Type*} [Fintype Ω] {n : ℕ}
    (R : FiniteLaw Ω) (θ : Ω → Fin n → Bool) (Z : α → ℝ)
    (hZ : ∀ a, 0 ≤ 1+Z a) (x : Fin n → α) :
    0 ≤ averagedDensity R θ Z x := by
  apply Finset.sum_nonneg
  intro ω _
  apply mul_nonneg (R.nonneg ω)
  apply Finset.prod_nonneg
  intro i _
  split_ifs
  · exact hZ _
  · norm_num

theorem averagedDensity_mono {α Ω : Type*} [Preorder α] [Fintype Ω] {n : ℕ}
    (R : FiniteLaw Ω) (θ : Ω → Fin n → Bool) (Z : α → ℝ)
    (hZ : ∀ a, 0 ≤ 1+Z a) (hZm : Monotone Z) :
    Monotone (averagedDensity R θ Z) := by
  intro x y hxy
  apply R.expect_mono
  intro ω
  apply Finset.prod_le_prod₀
  · intro i _
    split_ifs
    · exact hZ _
    · norm_num
  · intro i _
    split_ifs
    · linarith [hZm (hxy i)]
    · rfl

/-- Every independent-score likelihood product is normalized. -/
theorem selectionDensity_mean {α : Type*} [Fintype α] (P : FiniteLaw α)
    (Z : α → ℝ) (hZ : P.expect Z = 0) {n : ℕ} (θ : Fin n → Bool) :
    (P.product n).expect (selectionDensity θ Z) = 1 := by
  unfold FiniteLaw.expect FiniteLaw.product selectionDensity
  simp_rw [← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (i : Fin n) (a : α) => P.mass a * (if θ i then 1+Z a else 1))]
  apply Finset.prod_eq_one
  intro i _
  cases θ i
  · simp only [Bool.false_eq_true,↓reduceIte,mul_one,P.total]
  · simp only [↓reduceIte,mul_add,mul_one,Finset.sum_add_distrib,P.total]
    exact add_eq_left.mpr hZ

theorem averagedDensity_mean {α Ω : Type*} [Fintype α] [Fintype Ω]
    (P : FiniteLaw α) (R : FiniteLaw Ω) (Z : α → ℝ) (hZ : P.expect Z = 0)
    {n : ℕ} (θ : Ω → Fin n → Bool) :
    (P.product n).expect (averagedDensity R θ Z) = 1 := by
  unfold averagedDensity FiniteLaw.expect
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  have he (ω : Ω) : (∑ x : Fin n → α, (P.product n).mass x * (R.mass ω * selectionDensity (θ ω) Z x)) =
      R.mass ω * (P.product n).expect (selectionDensity (θ ω) Z) := by
    rw [FiniteLaw.expect,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring
  simp_rw [he,selectionDensity_mean P Z hZ,mul_one]
  exact R.total

end TraceReconstruction

namespace TraceReconstruction
open FiniteLaw

/-- Exact decomposition of the coefficient energy by its degree. -/
theorem multilinearEnergy_degrees {n : ℕ} (A : (Fin n → Bool) → ℝ) (R : ℝ) :
    multilinearEnergy A R = ∑ r ∈ Finset.range (n+1),
      R^(2*r) * ∑ σ : Fin n → Bool, if monomialDegree σ = r then A σ^2 else 0 := by
  classical
  unfold multilinearEnergy
  simp_rw [monomial_weight]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro σ _
  have hd : monomialDegree σ < n+1 := by
    have h := Finset.card_filter_le (s := Finset.univ) (p := fun i : Fin n => σ i = true)
    simpa [monomialDegree] using Nat.lt_succ_of_le h
  rw [Finset.sum_eq_single (monomialDegree σ)]
  · simp [mul_comm]
  · intro r _ hr
    simp [Ne.symm hr]
  · simp [Finset.mem_range,hd]

/-- A zero-degree selection is precisely the empty selection. -/
theorem monomialDegree_eq_zero_iff {n : ℕ} (σ : Fin n → Bool) :
    monomialDegree σ = 0 ↔ σ = fun _ => false := by
  classical
  constructor
  · intro h
    have he : Finset.univ.filter (fun i => σ i = true) = ∅ := Finset.card_eq_zero.mp h
    funext i
    have hn : σ i ≠ true := by
      intro hi
      have : i ∈ Finset.univ.filter (fun j => σ j = true) := by simp [hi]
      rw [he] at this
      exact Finset.notMem_empty i this
    exact Bool.eq_false_iff.mpr hn
  · rintro rfl
    simp [monomialDegree]

theorem averaged_degree_zero {Ω : Type*} [Fintype Ω] {n : ℕ}
    (R : FiniteLaw Ω) (θ : Ω → Fin n → Bool) :
    (∑ σ : Fin n → Bool, if monomialDegree σ = 0 then averagedCoefficient R θ σ ^ 2 else 0) = 1 := by
  classical
  simp_rw [monomialDegree_eq_zero_iff]
  simp [averagedCoefficient_empty]

/-- There is no increasing selection with more entries than its ambient set. -/
theorem increasingTuple_isEmpty {n r : ℕ} (h : n < r) : IsEmpty (IncreasingTuple n r) := by
  refine ⟨fun v => ?_⟩
  have hc := Fintype.card_le_of_injective v.val v.property.injective
  simp only [Fintype.card_fin] at hc
  omega

/-- The finite law of uniformly retained slots has no coefficients beyond
its number of actual defect slots. -/
theorem defect_degree_bound {n l u r : ℕ} (hl : l ≤ n)
    (d : Fin u → Fin n) (hd : StrictMono d) (hru : u < r) :
    (∑ σ : Fin l → Bool, if monomialDegree σ = r then
      averagedCoefficient (uniformSubsetLaw l (by simpa using hl))
        (defectAtRank (Finset.univ.image d)) σ ^ 2 else 0) = 0 := by
  classical
  apply le_antisymm
  · refine (sum_degree_coeff_sq_le (r:=r) (averagedCoefficient (uniformSubsetLaw l (by simpa using hl))
        (defectAtRank (Finset.univ.image d)))).trans ?_
    simp_rw [averaged_rank_coefficient hl d,rankDefectCoefficient_eq hl d hd]
    have := increasingTuple_isEmpty hru
    simp
  · apply Finset.sum_nonneg
    intro σ _
    split_ifs <;> positivity

/-- Coefficient version of the conditional-rank square-sum estimate. -/
theorem period_degree_square_sum {u m l r : ℕ} (hl : l ≤ u*m) (hr : 0 < r)
    (hru : r ≤ u) (hm : 32 ≤ m) (hum : u ≤ m) {δ θ : ℝ}
    (hδ : δ ∈ Set.Ioc 0 (1/2:ℝ))
    (hθ : θ ∈ Set.Icc (1-δ^2) (1-δ^2/4))
    (hmean : ((u*m:ℕ):ℝ)*θ=l) (hv : 1 ≤ ((u*m:ℕ):ℝ)*θ*(1-θ))
    (off : Fin u → Fin m)
    (hoff : ∀ j, |((off j).val:ℝ)-(m:ℝ)/2| ≤ 3)
    (hdiff : ∀ j k, |((off j).val:ℝ)-(off k).val| ≤ 2) :
    (∑ σ : Fin l → Bool, if monomialDegree σ = r then
      averagedCoefficient (uniformSubsetLaw l (by simpa using hl))
        (defectAtRank (Finset.univ.image (periodSlot off))) σ ^ 2 else 0) ≤
      ((3*rankSchurConstant/δ)*Real.sqrt ((u:ℝ)/((m:ℝ)*r)))^r := by
  refine (sum_degree_coeff_sq_le (r:=r) (averagedCoefficient (uniformSubsetLaw l (by simpa using hl))
    (defectAtRank (Finset.univ.image (periodSlot off))))).trans ?_
  simp_rw [averaged_rank_coefficient hl (periodSlot off),
    rankDefectCoefficient_eq hl (periodSlot off) (periodSlot_strictMono off)]
  exact period_rank_square_sum_delta hl hr hru hm hum hδ hθ hmean hv off hoff hdiff

/-- The full coefficient energy is controlled by the subgaussian degree
series, uniformly in the number of retained coordinates. -/
theorem period_density_energy {u m l : ℕ} (hl : l ≤ u*m)
    (hm : 32 ≤ m) (hum : u ≤ m) {δ θ : ℝ}
    (hδ : δ ∈ Set.Ioc 0 (1/2:ℝ))
    (hθ : θ ∈ Set.Icc (1-δ^2) (1-δ^2/4))
    (hmean : ((u*m:ℕ):ℝ)*θ=l) (hv : 1 ≤ ((u*m:ℕ):ℝ)*θ*(1-θ))
    (off : Fin u → Fin m)
    (hoff : ∀ j, |((off j).val:ℝ)-(m:ℝ)/2| ≤ 3)
    (hdiff : ∀ j k, |((off j).val:ℝ)-(off k).val| ≤ 2) (R : ℝ) :
    multilinearEnergy
      (averagedCoefficient (uniformSubsetLaw l (by simpa using hl))
        (defectAtRank (Finset.univ.image (periodSlot off)))) R ≤
      ∑ r ∈ Finset.range (l+1),
        (R^2*(3*rankSchurConstant/δ)*Real.sqrt ((u:ℝ)/m))^r / (Real.sqrt (r:ℝ))^r := by
  rw [multilinearEnergy_degrees]
  apply Finset.sum_le_sum
  intro r _
  by_cases hr : r = 0
  · subst r
    rw [averaged_degree_zero]
    norm_num
  · by_cases hru : r ≤ u
    · have hr0 : 0 < r := Nat.pos_of_ne_zero hr
      have hb := period_degree_square_sum hl hr0 hru hm hum hδ hθ hmean hv off hoff hdiff
      calc
        _ ≤ R^(2*r)*((3*rankSchurConstant/δ)*Real.sqrt ((u:ℝ)/((m:ℝ)*r)))^r :=
          mul_le_mul_of_nonneg_left hb (by rw [pow_mul]; positivity)
        _ = _ := by
          have hm0 : (0:ℝ) < m := by exact_mod_cast (show 0 < m by omega)
          have hr0 : (0:ℝ) < r := by exact_mod_cast hr0
          rw [show (u:ℝ)/((m:ℝ)*r)=((u:ℝ)/m)/r by field_simp]
          rw [Real.sqrt_div (by positivity),pow_mul,← mul_pow,← div_pow]
          congr 1
          ring
    · rw [defect_degree_bound hl (periodSlot off) (periodSlot_strictMono off) (by omega),mul_zero]
      have := hδ.1
      positivity [rankSchurConstant_pos]

/-- A convenient exponential majorant for the full nonnegative degree series. -/
theorem degree_series_le_exp (a : ℝ) (N : ℕ) :
    (∑ r ∈ Finset.range N, a^r / (Real.sqrt (r:ℝ))^r) ≤ 2*Real.exp (a^2) := by
  have hb := degree_series_bound a N
  have hp := Real.exp_pos (a^2)
  have he : Real.exp (2*a^2) = (Real.exp (a^2))^2 := by
    rw [show 2*a^2=a^2+a^2 by ring,Real.exp_add]
    ring
  rw [he] at hb
  nlinarith [sq_nonneg ((∑ r ∈ Finset.range N, a^r / (Real.sqrt (r:ℝ))^r)+2*Real.exp (a^2))]

/-- Actual conditional initial-oracle density, with its exact second moment. -/
theorem period_density_second_moment {α : Type*} [Fintype α]
    (P : FiniteLaw α) (Z : α → ℝ) (hZ : P.expect Z = 0)
    {u m l : ℕ} (hl : l ≤ u*m)
    (hm : 32 ≤ m) (hum : u ≤ m) {δ θ : ℝ}
    (hδ : δ ∈ Set.Ioc 0 (1/2:ℝ))
    (hθ : θ ∈ Set.Icc (1-δ^2) (1-δ^2/4))
    (hmean : ((u*m:ℕ):ℝ)*θ=l) (hv : 1 ≤ ((u*m:ℕ):ℝ)*θ*(1-θ))
    (off : Fin u → Fin m)
    (hoff : ∀ j, |((off j).val:ℝ)-(m:ℝ)/2| ≤ 3)
    (hdiff : ∀ j k, |((off j).val:ℝ)-(off k).val| ≤ 2) :
    (P.product l).expect (fun x =>
      averagedDensity (uniformSubsetLaw l (by simpa using hl))
        (defectAtRank (Finset.univ.image (periodSlot off))) Z x ^ 2) ≤
      2*Real.exp ((P.expect (fun a => Z a^2))^2 * (3*rankSchurConstant/δ)^2 * ((u:ℝ)/m)) := by
  have hv0 : 0 ≤ P.expect (fun a => Z a^2) :=
    Finset.sum_nonneg (fun a _ => mul_nonneg (P.nonneg a) (sq_nonneg _))
  simp_rw [averagedDensity_expansion]
  rw [multilinear_second_moment P Z hZ (Real.sqrt (P.expect (fun a => Z a^2)))
    (Real.sq_sqrt hv0).symm]
  refine (period_density_energy hl hm hum hδ hθ hmean hv off hoff hdiff _).trans ?_
  apply (degree_series_le_exp _ (l+1)).trans
  rw [Real.sq_sqrt hv0]
  have he : (P.expect (fun a => Z a^2)*(3*rankSchurConstant/δ)*Real.sqrt ((u:ℝ)/m))^2 =
      (P.expect (fun a => Z a^2))^2*(3*rankSchurConstant/δ)^2*((u:ℝ)/m) := by
    rw [mul_pow,mul_pow,Real.sq_sqrt (by positivity)]
  rw [he]

/-- The source association argument holds for any two conditional mixture
experiments using the same independent primitive marks, even when their
retained-subset sample spaces have different original sizes. -/
theorem averagedDensity_overlap {α Ω Ψ : Type*}
    [Fintype α] [Fintype Ω] [Fintype Ψ]
    (P : FiniteLaw α) (R : FiniteLaw Ω) (S : FiniteLaw Ψ)
    (Z : α → ℝ) (hZ : P.expect Z = 0) (hZpos : ∀ a, 0 ≤ 1+Z a)
    {l : ℕ} (f : Ω → Fin l → Bool) (g : Ψ → Fin l → Bool) :
    (1:ℝ)/32 ≤
      (P.product l).expect (fun x => min (averagedDensity R f Z x) (averagedDensity S g Z x)) *
      (P.product l).expect (fun x => averagedDensity R f Z x ^ 2) *
      (P.product l).expect (fun x => averagedDensity S g Z x ^ 2) := by
  let : Preorder α := Preorder.lift Z
  have htotal : ∀ a b : α, a ≤ b ∨ b ≤ a := fun a b => le_total (Z a) (Z b)
  have hm : Monotone Z := fun _ _ h => h
  exact increasing_density_overlap (P.product l)
    (associated_product P (P.associated_totalPreorder htotal) l)
    (averagedDensity R f Z) (averagedDensity S g Z)
    (averagedDensity_nonneg R f Z hZpos) (averagedDensity_nonneg S g Z hZpos)
    (averagedDensity_mono R f Z hZpos hm) (averagedDensity_mono S g Z hZpos hm)
    (averagedDensity_mean P R Z hZ f) (averagedDensity_mean P S Z hZ g)

end TraceReconstruction

end
end
end

end OAI
