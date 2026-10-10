import Mathlib
import OAI.Combinatorics.SharpRamsey.Marking.TailSum

namespace OAI

/-! High-rank geometric supports and entropy estimates. -/

section
open scoped BigOperators Classical
open Finset
namespace SharpLogRamsey.HighRankExcess
open scoped BigOperators
open Finset Classical
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable [Finite K] [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
omit [Finite K] [FiniteDimensional K V] in
lemma target_event_eq (U : Finset (Projectivization K V))
    (W : Projectivization K V → Submodule K V) (r : ℕ)
    (p : Projectivization K V × Projectivization K (Module.Dual K V) → ℝ)
    (hsupp : ∀ z, p z≠0 → z.1 ∈ U) :
    (∑ z, p z*(if r < Module.finrank K (W z.1) ∧ W z.1 ≤ LinearMap.ker z.2.rep
      then 1 else 0)) = ∑ z ∈ excessCarrier U W r, p z := by
  let E (z : Projectivization K V × Projectivization K (Module.Dual K V)) :=
    r < Module.finrank K (W z.1) ∧ W z.1 ≤ LinearMap.ker z.2.rep
  have he (z : Projectivization K V × Projectivization K (Module.Dual K V)) :
      p z*(if E z then 1 else 0) =
      if z ∈ U ×ˢ univ then (if E z then p z else 0) else 0 := by
    by_cases hpz : p z=0
    · simp [hpz]
    · simp [hsupp z hpz, mul_ite]
  change (∑ z, p z*(if E z then 1 else 0)) = _
  simp_rw [he]
  rw [excessCarrier, sum_filter]
  rw [← sum_filter]
  simp only [filter_mem_eq_inter, univ_inter]
  rfl

omit [Fintype (Projectivization K V)] in
lemma target_excess_mass_sharp {d r : ℕ} (hdim : Module.finrank K V = d+1) (hr : r ≤ d)
    (U : Finset (Projectivization K V)) (W : Projectivization K V → Submodule K V)
    (p : Projectivization K V × Projectivization K (Module.Dual K V) → ℝ)
    (hp : ∀ z, 0 ≤ p z) (M : ℝ) (hM : 0 ≤ M) :
    (∑ z ∈ excessCarrier U W r, p z) ≤
      (∑ z ∈ U ×ˢ univ, if M < p z then p z else 0) +
        (if r<d then U.card*(2*(Nat.card K:ℝ)^(d-r-1))*M else 0) := by
  obtain hrd | rfl := hr.lt_or_eq
  · rw [ite_eq_left hrd]
    exact target_excess_mass hdim hrd U W p hp M hM
  · rw [ite_eq_right (lt_irrefl _), add_zero, excessCarrier_full_rank hdim, sum_empty]
    apply sum_nonneg
    intro z _
    split_ifs <;> first | exact hp _ | rfl

end
end SharpLogRamsey.HighRankExcess

namespace SharpLogRamsey.ProductLaw
open scoped BigOperators
open Finset Classical
noncomputable section
variable {ι κ Ω : Type*} [Fintype ι] [Fintype κ] [Fintype Ω]

noncomputable def weight (w : Ω → ℝ) (z : ι → Ω) : ℝ := ∏ i, w (z i)

omit [Fintype κ] in
lemma total (w : Ω → ℝ) (ht : ∑ x, w x = 1) : ∑ z : ι → Ω, weight w z = 1 := by
  unfold weight
  rw [← Fintype.prod_sum]
  simp [ht]

omit [Fintype κ] [Fintype Ω] in
lemma nonneg (w : Ω → ℝ) (hw : ∀ a, 0 ≤ w a) (z : ι → Ω) : 0 ≤ weight w z :=
  prod_nonneg (fun i _ => hw (z i))

lemma reindex (w : Ω → ℝ) (e : ι ≃ κ) (f : (κ → Ω) → ℝ) :
    (∑ z : ι → Ω, weight w z*f (z ∘ e.symm)) = ∑ z : κ → Ω, weight w z*f z := by
  let E : (κ → Ω) ≃ (ι → Ω) := Equiv.arrowCongr e.symm (Equiv.refl Ω)
  rw [← E.sum_comp]
  apply sum_congr rfl
  intro z _
  have hfun : E z ∘ e.symm = z := by funext i; simp [E]
  rw [hfun]
  congr 1
  unfold weight
  simpa [E] using e.prod_comp (fun i => w (z i))

omit [Fintype κ] in
lemma restriction (w : Ω → ℝ) (ht : ∑ x, w x = 1)
    (P : ι → Prop) (f : ({i // P i} → Ω) → ℝ) :
    (∑ z : ι → Ω, weight w z*f (fun i => z i)) =
      ∑ z : {i // P i} → Ω, weight w z*f z := by
  let E := Equiv.piEquivPiSubtypeProd P (fun _ : ι => Ω)
  rw [← E.symm.sum_comp]
  simp only [Fintype.sum_prod_type]
  have hsplit (z : {i // P i} → Ω) (z' : {i // ¬P i} → Ω) :
      weight w (E.symm (z,z')) = weight w z*weight w z' := by
    unfold weight
    rw [← Fintype.prod_subtype_mul_prod_subtype P]
    congr 1
    · apply prod_congr rfl
      intro i _
      simp [E, i.property]
    · apply prod_congr rfl
      intro i _
      simp [E, i.property]
  have hres (z : {i // P i} → Ω) (z' : {i // ¬P i} → Ω) :
      (fun i : {i // P i} => E.symm (z,z') i) = z := by
    funext i
    simp [E, i.property]
  simp_rw [hsplit, hres]
  apply sum_congr rfl
  intro z _
  calc
    _ = weight w z*f z*(∑ z' : {i // ¬P i} → Ω, weight w z') := by
      rw [mul_sum]
      apply sum_congr rfl
      intro z' _
      ring
    _ = _ := by
      have hz : (∑ z' : {i // ¬P i} → Ω, weight w z') = 1 := by
        unfold weight
        rw [← Fintype.prod_sum]
        simp [ht]
      rw [hz, mul_one]

lemma marginal (w : Ω → ℝ) (ht : ∑ x, w x = 1) (e : κ ↪ ι)
    (f : (κ → Ω) → ℝ) :
    (∑ z : ι → Ω, weight w z*f (z ∘ e)) = ∑ z : κ → Ω, weight w z*f z := by
  let E : κ ≃ {i // i ∈ Set.range e} := Equiv.ofInjective e e.injective
  have h := restriction w ht (fun i => i ∈ Set.range e)
    (fun z => f (z ∘ E))
  change (∑ z : ι → Ω, weight w z*f (z ∘ e)) = _ at h
  rw [h]
  convert reindex w E.symm f using 1
  simp only [Equiv.symm_symm]
  congr!

omit [Fintype κ] in
lemma coordinate_mean (w : Ω → ℝ) (ht : ∑ x, w x = 1)
    (i : ι) (f : Ω → ℝ) :
    (∑ z : ι → Ω, weight w z*f (z i)) = ∑ x, w x*f x := by
  have hi (z : ι → Ω) : weight w z*f (z i) =
      ∏ j, w (z j)*(if j=i then f (z j) else 1) := by
    rw [prod_mul_distrib]
    simp [weight]
  simp_rw [hi]
  rw [← Fintype.prod_sum (fun j x => w x*(if j=i then f x else 1))]
  have he (j : ι) : (∑ x, w x*(if j=i then f x else 1)) =
      if j=i then ∑ x, w x*f x else 1 := by
    split_ifs <;> simp_all
  simp_rw [he]
  simp

omit [Fintype κ] in

lemma row_exists_le (w : Ω → ℝ) (hw : ∀ x, 0 ≤ w x)
    (ht : ∑ x, w x = 1) (E : Ω → Prop) :
    (∑ z : ι → Ω, weight w z*(if ∃ i, E (z i) then 1 else 0)) ≤
      (Fintype.card ι:ℝ)*(∑ x, w x*(if E x then 1 else 0)) := by
  calc
    _ ≤ ∑ z : ι → Ω, weight w z*(∑ i : ι, if E (z i) then 1 else 0) := by
      apply sum_le_sum
      intro z _
      apply mul_le_mul_of_nonneg_left _ (nonneg w hw z)
      split_ifs with h
      · obtain ⟨i,hi⟩ := h
        have H := single_le_sum (fun j (_ : j ∈ (univ : Finset ι)) =>
          show (0:ℝ) ≤ if E (z j) then 1 else 0 by split_ifs <;> norm_num) (mem_univ i)
        simpa only [ite_eq_left hi] using H
      · apply sum_nonneg
        intro i _
        split_ifs <;> norm_num
    _ = ∑ i : ι, ∑ z : ι → Ω, weight w z*(if E (z i) then 1 else 0) := by
      simp_rw [mul_sum]
      exact sum_comm
    _ = ∑ _i : ι, (∑ x, w x*(if E x then 1 else 0)) := by
      apply sum_congr rfl
      intro i _
      exact coordinate_mean w ht i (fun x => if E x then 1 else 0)
    _ = _ := by simp

end
end SharpLogRamsey.ProductLaw

namespace SharpLogRamsey.FiniteMarginals
open scoped BigOperators
open Finset Classical
noncomputable section
variable {Ω Y ι : Type*} [Fintype Ω] [Fintype Y] [Fintype ι]

omit [Fintype Y] [Fintype ι] in
def marginal (w : Ω → ℝ) (f : Ω → Y) (y : Y) : ℝ := ∑ z, if f z=y then w z else 0

omit [Fintype ι] in
lemma sum_marginal (w : Ω → ℝ) (f : Ω → Y) (g : Y → ℝ) :
    (∑ y, marginal w f y*g y) = ∑ z, w z*g (f z) := by
  unfold marginal
  simp_rw [sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro z _
  simp

omit [Fintype ι] in
lemma marginal_total (w : Ω → ℝ) (f : Ω → Y) : ∑ y, marginal w f y=∑ z, w z := by
  simpa using sum_marginal w f (fun _ => 1)

omit [Fintype Y] [Fintype ι] in
lemma marginal_nonneg (w : Ω → ℝ) (hw : ∀ z, 0 ≤ w z) (f : Ω → Y) (y : Y) :
    0 ≤ marginal w f y := by
  apply sum_nonneg
  intro z _
  split_ifs
  · exact hw z
  · exact le_rfl

omit [Fintype Y] in
lemma row_mass (w : Ω → ℝ) (f : Ω → Y) (u : ι → Y) :
    ProductLaw.weight (marginal w f) u =
      ∑ z : ι → Ω, ProductLaw.weight w z*(if (fun i => f (z i))=u then 1 else 0) := by
  unfold ProductLaw.weight marginal
  rw [Fintype.prod_sum]
  apply sum_congr rfl
  intro z _
  by_cases he : (fun i => f (z i))=u
  · have hp : ∀ i, f (z i)=u i := congrFun he
    simp [hp]
  · rw [ite_eq_right he, mul_zero]
    obtain ⟨i, hi⟩ : ∃ i, f (z i)≠u i := by
      by_contra hh
      push Not at hh
      exact he (funext hh)
    exact prod_eq_zero (mem_univ i) (ite_eq_right hi)

lemma row_pushforward (w : Ω → ℝ) (f : Ω → Y) (F : (ι → Y) → ℝ) :
    (∑ z : ι → Ω, ProductLaw.weight w z*F (fun i => f (z i))) =
      ∑ u : ι → Y, ProductLaw.weight (marginal w f) u*F u := by
  simp_rw [row_mass, sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro z _
  simp

end
end SharpLogRamsey.FiniteMarginals

namespace SharpLogRamsey.HighRankSize
open scoped BigOperators
open Finset Classical HighRankDecoder RichUnion FiniteMarginals
noncomputable section
variable {K Ω : Type*} [Field K] [Fintype K] [Fintype Ω] {n : ℕ}
local instance flat_JoinedHighRankAssembly_2 : Fintype (Projectivization K (Fin n → K)) := Fintype.ofFinite _
local instance flat_JoinedHighRankAssembly_3 : Finite (Module.Dual K (Fin n → K)) :=
  Finite.of_injective ((↑) : Module.Dual K (Fin n → K) → ((Fin n → K) → K)) DFunLike.coe_injective
local instance flat_JoinedHighRankAssembly_4 : Fintype (Projectivization K (Module.Dual K (Fin n → K))) := Fintype.ofFinite _

def rankPoints {h : ℕ} (a : Ω → Module.Dual K (Fin n → K))
    (b : Ω → Projectivization K (Fin n → K)) (z₁ : Fin h → Ω) (r : ℕ) :=
  univ.filter (fun y => Module.finrank K (hitSpan a b y z₁)=r)

def points {h : ℕ} (a : Ω → Module.Dual K (Fin n → K))
    (b : Ω → Projectivization K (Fin n → K)) (z₁ z₂ : Fin h → Ω) (r T : ℕ) :=
  (rankPoints a b z₁ r).filter (fun y =>
    T ≤ (univ.filter (fun i => (b (z₂ i)).submodule ≤ hitSpan a b y z₁)).card)

def domain {h : ℕ} (a : Ω → Module.Dual K (Fin n → K))
    (b : Ω → Projectivization K (Fin n → K)) (z₁ z₂ : Fin h → Ω) (r T : ℕ) :
    Finset (Projectivization K (Fin n → K) × Projectivization K (Module.Dual K (Fin n → K))) :=
  univ.filter (fun t => Admitted a b z₁ z₂ r T t.1 t.2)

omit [Fintype Ω] in
lemma partner_bound {r : ℕ} (hr : r<n) (W : Submodule K (Fin n → K))
    (hW : Module.finrank K W=r) :
    ((HighRankExcess.partners W).card:ℝ) ≤ 2*(Fintype.card K:ℝ)^(n-r-1) := by
  rw [HighRankExcess.partners_eq, ← (Nat.card_eq_fintype_card (α := K))]
  apply HighRankExcess.small_span_card (n-r) (by omega)
  have H := Subspace.finrank_add_finrank_dualAnnihilator_eq W
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at H
  omega

omit [Fintype Ω] in
lemma domain_card {h r : ℕ} (hr : r<n) (a : Ω → Module.Dual K (Fin n → K))
    (b : Ω → Projectivization K (Fin n → K)) (z₁ z₂ : Fin h → Ω) (T : ℕ) :
    ((domain a b z₁ z₂ r T).card:ℝ) ≤
      ((points a b z₁ z₂ r T).card:ℝ)*(2*(Fintype.card K:ℝ)^(n-r-1)) := by
  have he : domain a b z₁ z₂ r T =
      (points a b z₁ z₂ r T).biUnion (fun y =>
        (HighRankExcess.partners (hitSpan a b y z₁)).image (Prod.mk y)) := by
    ext t
    simp only [domain, points, rankPoints, HighRankExcess.partners]
    simp only [mem_filter, mem_univ, true_and, mem_biUnion, mem_image]
    change (Admitted a b z₁ z₂ r T t.1 t.2) ↔ _
    unfold Admitted
    constructor
    · rintro ⟨hR,hC,hT⟩
      exact ⟨t.1,⟨hR,hT⟩,t.2,hC,rfl⟩
    · rintro ⟨y,⟨hR,hT⟩,c,hC,he⟩
      cases he
      exact ⟨hR,hC,hT⟩
  rw [he]
  calc
    _ ≤ ∑ y ∈ points a b z₁ z₂ r T,
        (((HighRankExcess.partners (hitSpan a b y z₁)).image (Prod.mk y)).card:ℝ) := by
      exact_mod_cast card_biUnion_le
    _ ≤ ∑ _y ∈ points a b z₁ z₂ r T, 2*(Fintype.card K:ℝ)^(n-r-1) := by
      apply sum_le_sum
      intro y hy
      rw [card_image_of_injective _ (by intro c c' hh; exact (Prod.mk.inj hh).2)]
      exact partner_bound hr _ (mem_filter.mp (mem_filter.mp hy).1).2
    _ = _ := by simp

lemma mean_points {h : ℕ} (w : Ω → ℝ) (a : Ω → Module.Dual K (Fin n → K))
    (b : Ω → Projectivization K (Fin n → K)) (z₁ : Fin h → Ω) (r T : ℕ) :
    (∑ z₂ : Fin h → Ω, ProductLaw.weight w z₂*((points a b z₁ z₂ r T).card:ℝ)) =
      ∑ y ∈ rankPoints a b z₁ r, FiniteSamplingBounds.rowTail (marginal w b)
        (projectivePoints (hitSpan a b y z₁)) h T := by
  let F (z : Fin h → Projectivization K (Fin n → K)) : ℝ :=
    (((rankPoints a b z₁ r).filter (fun y => T ≤
      FiniteSamplingBounds.hitCount (projectivePoints (hitSpan a b y z₁)) z)).card:ℝ)
  have he : ∀ z₂, ((points a b z₁ z₂ r T).card:ℝ) = F (fun i => b (z₂ i)) := by
    intro z₂
    simp only [F, points, FiniteSamplingBounds.hitCount, mem_projectivePoints]
  simp_rw [he]
  have H := row_pushforward (ι := Fin h) w b F
  calc
    _ = ∑ z : Fin h → Projectivization K (Fin n → K),
        ProductLaw.weight (marginal w b) z*F z := by
      convert H using 1
      congr!
      · congr 1
        ext z
        simp
    _ = _ := by
      convert HighRankSampling.mean_admitted_eq (marginal w b)
        (rankPoints a b z₁ r) (fun y => hitSpan a b y z₁) h T using 1
      congr!

theorem expected_domain {h r T : ℕ} (hn : 0<n) (hr : 0<r) (hrn : r<n)
    (w : Ω → ℝ) (hw : ∀ z, 0 ≤ w z) (ht : ∑ z, w z=1)
    (a : Ω → Module.Dual K (Fin n → K)) (b : Ω → Projectivization K (Fin n → K))
    (z₁ : Fin h → Ω) (X : Finset (Projectivization K (Fin n → K)))
    (hsupp : ∀ x, x∉X → marginal w b x=0)
    (A u : ℝ) (hA : 0<A) (hu : 0<u) (huA : u ≤ 2*A)
    (hu20 : u≤1/20) (hCu : 20*Real.exp (1/2)*u≤1)
    (hcap : ∀ x ∈ X, marginal w b x ≤ A/(Fintype.card K:ℝ)^r)
    (hT : (h:ℝ)/(10*(Fintype.card K:ℝ))≤T) (hTn : n+1≤T) :
    (∑ z₂ : Fin h → Ω, ProductLaw.weight w z₂*((domain a b z₁ z₂ r T).card:ℝ)) ≤
      (10*(n:ℝ)*A/u)^n*X.card*(1+2^(n+1))*(2*(Fintype.card K:ℝ)^(n-r-1)) := by
  have H := HighRankSampling.high_rank_expected hn (marginal w b)
    (marginal_nonneg w hw b) (by rw [marginal_total,ht]) X (rankPoints a b z₁ r)
    hsupp A u hA hu huA hu20 hCu r hr hcap (fun y => hitSpan a b y z₁)
    (fun y hy => (mem_filter.mp hy).2) (fun y _ => center_le a b y z₁) h T hT hTn
  calc
    _ ≤ ∑ z₂ : Fin h → Ω, ProductLaw.weight w z₂*
        (((points a b z₁ z₂ r T).card:ℝ)*(2*(Fintype.card K:ℝ)^(n-r-1))) := by
      apply sum_le_sum
      intro z₂ _
      exact mul_le_mul_of_nonneg_left (domain_card hrn a b z₁ z₂ T) (ProductLaw.nonneg w hw z₂)
    _ = (∑ z₂ : Fin h → Ω, ProductLaw.weight w z₂*((points a b z₁ z₂ r T).card:ℝ))*
        (2*(Fintype.card K:ℝ)^(n-r-1)) := by simp only [← mul_assoc, sum_mul]
    _ ≤ _ := by
      rw [mean_points]
      exact mul_le_mul_of_nonneg_right H (by positivity)

end
end SharpLogRamsey.HighRankSize

namespace SharpLogRamsey.FiniteRowProcess
open scoped BigOperators
open Finset Classical
noncomputable section
variable {Ω X : Type*} [Fintype Ω]

def weight (w : Ω → ℝ) {n : ℕ} (z : Fin n → Ω) : ℝ := ∏ i, w (z i)

omit [Fintype Ω] in
lemma weight_nonneg (w : Ω → ℝ) (hw : ∀ a, 0 ≤ w a) {n : ℕ} (z : Fin n → Ω) :
    0 ≤ weight w z := prod_nonneg (fun _ _ => hw _)

lemma weight_total (w : Ω → ℝ) (hw : ∑ a, w a = 1) (n : ℕ) :
    ∑ z : Fin n → Ω, weight w z = 1 := by
  unfold weight
  rw [← Fintype.prod_sum]
  simp [hw]

def run (step : X → Ω → X) : (n : ℕ) → (Fin n → Ω) → X → X
  | 0, _, x => x
  | n+1, z, x => run step n (Fin.tail z) (step x (z 0))

def expected (w : Ω → ℝ) (step : X → Ω → X) (n : ℕ) (x : X) (f : X → ℝ) : ℝ :=
  ∑ z : Fin n → Ω, weight w z * f (run step n z x)

lemma expected_zero (w : Ω → ℝ) (step : X → Ω → X) (x : X) (f : X → ℝ) :
    expected w step 0 x f = f x := by simp [expected, weight, run]

lemma expected_succ (w : Ω → ℝ) (step : X → Ω → X) (n : ℕ) (x : X) (f : X → ℝ) :
    expected w step (n+1) x f = ∑ a, w a * expected w step n (step x a) f := by
  unfold expected
  rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (n+1) => Ω))
    (fun z => weight w z * f (run step (n+1) z x))]
  simp only [Fintype.sum_prod_type]
  change (∑ a, ∑ z, weight w (Fin.cons a z) * f (run step (n+1) (Fin.cons a z) x)) = _
  simp only [run, Fin.cons_zero, Fin.tail_cons, weight, Fin.prod_univ_succ, Fin.cons_succ]
  simp only [mul_assoc, mul_sum]

lemma expected_le_one (w : Ω → ℝ) (hw : ∀ a, 0 ≤ w a) (ht : ∑ a, w a = 1)
    (step : X → Ω → X) (n : ℕ) (x : X) (f : X → ℝ) (hf : ∀ x, f x ≤ 1) :
    expected w step n x f ≤ 1 := by
  rw [← weight_total w ht n]
  apply sum_le_sum
  intro z _
  exact mul_le_of_le_one_right (weight_nonneg w hw z) (hf _)

omit [Fintype Ω] in
lemma rank_run (step : X → Ω → X) (rank : X → ℕ)
    (hmono : ∀ x a, rank x ≤ rank (step x a)) (n : ℕ) (z : Fin n → Ω) (x : X) :
    rank x ≤ rank (run step n z x) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => exact (hmono x (z 0)).trans (ih (Fin.tail z) _)

theorem rank_reached (w : Ω → ℝ) (hw : ∀ a, 0 ≤ w a) (ht : ∑ a, w a = 1)
    (step : X → Ω → X) (rank : X → ℕ) (r : ℕ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hmono : ∀ x a, rank x ≤ rank (step x a))
    (hbad : ∀ x, rank x < r →
      (∑ a, w a * (if rank (step x a) ≤ rank x then 1 else 0)) ≤ δ)
    (n : ℕ) (x : X) (hx : r ≤ rank x+n) :
    expected w step n x (fun y => if rank y < r then 1 else 0) ≤ n*δ := by
  induction n generalizing x with
  | zero =>
    rw [expected_zero]
    simp only [Nat.add_zero] at hx
    simp [Nat.not_lt.mpr hx]
  | succ n ih =>
    by_cases hxr : r ≤ rank x
    · have hz : expected w step (n+1) x (fun y => if rank y < r then 1 else 0) = 0 := by
        apply sum_eq_zero
        intro z _
        simp [Nat.not_lt.mpr (hxr.trans (rank_run step rank hmono _ z x))]
      rw [hz]
      positivity
    · have hb := hbad x (Nat.lt_of_not_ge hxr)
      rw [expected_succ]
      calc
        _ ≤ ∑ a, w a * ((n:ℝ)*δ + if rank (step x a) ≤ rank x then 1 else 0) := by
          apply sum_le_sum
          intro a _
          apply mul_le_mul_of_nonneg_left _ (hw a)
          by_cases ha : rank (step x a) ≤ rank x
          · rw [ite_eq_left ha]
            exact (expected_le_one w hw ht step n (step x a) _ (by intro y; split_ifs <;> norm_num)).trans
              (by nlinarith [show (0:ℝ) ≤ n from Nat.cast_nonneg n])
          · rw [ite_eq_right ha, add_zero]
            apply ih
            omega
        _ = (n:ℝ)*δ + ∑ a, w a * (if rank (step x a) ≤ rank x then 1 else 0) := by
          simp only [mul_add, sum_add_distrib, ← sum_mul, ht, one_mul]
        _ ≤ (n:ℝ)*δ+δ := add_le_add_right hb _
        _ = (n+1:ℕ)*δ := by push_cast; ring

end
end SharpLogRamsey.FiniteRowProcess

namespace SharpLogRamsey.HighRankCoverage
open scoped BigOperators
open Finset Classical FiniteRowProcess
noncomputable section
variable {Ω K V : Type*} [Fintype Ω] [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

end
end SharpLogRamsey.HighRankCoverage
end

end OAI
