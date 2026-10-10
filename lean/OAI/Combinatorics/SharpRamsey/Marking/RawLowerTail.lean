import Mathlib
import OAI.Combinatorics.SharpRamsey.Marking.RowSpan

namespace OAI

/-! High-rank geometric supports and entropy estimates. -/

section
open scoped BigOperators Classical
open Finset
namespace SharpLogRamsey.HighRankCoverageProbability
open scoped BigOperators
open Finset Classical FiniteEventBounds HighRankDecoder
noncomputable section
variable {K V Ω : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K] [Fintype (Projectivization K V)] [Fintype Ω]
omit [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [Finite K] [Fintype (Projectivization K V)] in
lemma raw_lower_tail (w : Ω → ℝ) (hw : ∀ z, 0 ≤ w z)
    (ht : ∑ z, w z=1) (Q : Ω → Prop) (q : ℝ) (hq : 0<q) (h T : ℕ)
    (hE : 2/(5*q) ≤ ∑ z ∈ univ.filter Q, w z)
    (hT : (T:ℝ) ≤ (h:ℝ)/(10*q)+1) :
    (∑ z : Fin h → Ω, ProductLaw.weight w z *
      indicator ((univ.filter (fun i => Q (z i))).card < T)) ≤
      Real.exp (1-(h:ℝ)/(10*q)) := by
  have hl := FiniteSamplingBounds.rowLower_highRank w hw ht (univ.filter Q) h T q hq hE hT
  convert hl using 1
  simp [FiniteSamplingBounds.rowLower, FiniteSamplingBounds.hitCount,
    FiniteSamplingBounds.rowWeight, ProductLaw.weight, indicator, mul_ite]

theorem fixed_query_bound (w : Ω → ℝ) (hw : ∀ z, 0 ≤ w z)
    (ht : ∑ z, w z=1) (a : Ω → Module.Dual K V) (b : Ω → Projectivization K V)
    (y : Projectivization K V) (c : Projectivization K (Module.Dual K V))
    (hcy : c.rep y.rep=0) (h r m T : ℕ) (e : Fin r × Fin m ↪ Fin h) (hr : 2 ≤ r)
    (M : ℝ) (hM0 : 0 ≤ M)
    (hM : ∀ u, (∑ z ∈ univ.filter (fun z => b z=u), w z) ≤ M)
    (hE : 2/(5*(Nat.card K:ℝ)) ≤ ∑ z ∈ univ.filter (fun z => a z y.rep=0), w z)
    (hT : (T:ℝ) ≤ (h:ℝ)/(10*(Nat.card K:ℝ))+1) :
    mean2 (ProductLaw.weight w : (Fin h → Ω) → ℝ) (ProductLaw.weight w : (Fin h → Ω) → ℝ)
        (fun z₁ z₂ => indicator (¬Admitted a b z₁ z₂ r T y c)) ≤
      r*(1-(2/(5*(Nat.card K:ℝ))-2*M*(Nat.card K:ℝ)^(r-2)))^m+
      Real.exp (1-(h:ℝ)/(10*(Nat.card K:ℝ)))+2*h*conflictMass w a b y c+
      mean2 (ProductLaw.weight w : (Fin h → Ω) → ℝ) (ProductLaw.weight w : (Fin h → Ω) → ℝ)
        (fun z₁ z₂ => indicator
          (r < Module.finrank K (hitSpan a b y z₁ ⊔ hitSpan a b y z₂ : Submodule K V) ∧
           hitSpan a b y z₁ ⊔ hitSpan a b y z₂ ≤ LinearMap.ker c.rep)) := by
  have hq : (0:ℝ) < Nat.card K := by exact_mod_cast Nat.card_pos
  have hH : (∑ z ∈ univ.filter (fun z => a z y.rep=0), w z) =
      ∑ z, w z*(if a z y.rep=0 then 1 else 0) := by
    simp [sum_filter, mul_ite]
  have hH1 : 2/(5*(Nat.card K:ℝ)) ≤ 1 := by
    apply hE.trans
    rw [← ht]
    exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (by intros; exact hw _)
  have hg := HighRankGrowth.raw_row_span_growth w hw ht a b y h r m e hr
    (2/(5*(Nat.card K:ℝ))) M hM0 hM (by rwa [← hH]) hH1
  have hl := raw_lower_tail w hw ht (fun z => a z y.rep=0) (Nat.card K:ℝ) hq h T hE hT
  have hc := ProductLaw.row_exists_le (ι := Fin h) w hw ht
    (fun z => a z y.rep=0 ∧ c.rep (b z).rep≠0)
  simp only [Fintype.card_fin] at hc
  apply (raw_coverage_union w hw ht a b y c hcy h r T).trans
  refine add_le_add ?_ le_rfl
  have hh := add_le_add (add_le_add hg hl) (mul_le_mul_of_nonneg_left hc (by norm_num : (0:ℝ) ≤ 2))
  convert hh using 1 <;> simp only [indicator, conflictMass, mul_assoc]
  congr!

end
end SharpLogRamsey.HighRankCoverageProbability

namespace SharpLogRamsey.HighRankAveraged
open scoped BigOperators
open Finset Classical FiniteEventBounds HighRankDecoder HighRankCoverageProbability
noncomputable section
variable {K V Ω : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K] [Fintype (Projectivization K V)]
  [Fintype (Projectivization K (Module.Dual K V))] [Fintype Ω]

theorem excess_average (w : Ω → ℝ) (hw : ∀ z, 0 ≤ w z) (ht : ∑ z, w z=1)
    (p : Projectivization K V × Projectivization K (Module.Dual K V) → ℝ)
    (hp : ∀ z, 0 ≤ p z) (U : Finset (Projectivization K V))
    (hsupp : ∀ z, p z≠0 → z.1 ∈ U)
    (a : Ω → Module.Dual K V) (b : Ω → Projectivization K V)
    (h d r : ℕ) (hdim : Module.finrank K V=d+1) (hr : r ≤ d)
    (J : ℝ) (hJ : 0 ≤ J) :
    (∑ t, p t*mean2 (ProductLaw.weight w : (Fin h → Ω) → ℝ)
      (ProductLaw.weight w : (Fin h → Ω) → ℝ)
      (fun z₁ z₂ => indicator
        (r < Module.finrank K (hitSpan a b t.1 z₁ ⊔ hitSpan a b t.1 z₂ : Submodule K V) ∧
         hitSpan a b t.1 z₁ ⊔ hitSpan a b t.1 z₂ ≤ LinearMap.ker t.2.rep))) ≤
      (∑ t ∈ U ×ˢ univ, if J < p t then p t else 0)+
        (if r<d then U.card*(2*(Nat.card K:ℝ)^(d-r-1))*J else 0) := by
  rw [mean2_sum]
  have hnt : ∑ z : Fin h → Ω, ProductLaw.weight w z=1 := by
    convert ProductLaw.total (ι := Fin h) w ht using 1
    congr!
  have H : ∀ z₁ z₂ : Fin h → Ω,
      (∑ t, p t* indicator
        (r < Module.finrank K (hitSpan a b t.1 z₁ ⊔ hitSpan a b t.1 z₂ : Submodule K V) ∧
         hitSpan a b t.1 z₁ ⊔ hitSpan a b t.1 z₂ ≤ LinearMap.ker t.2.rep)) ≤
      (∑ t ∈ U ×ˢ univ, if J < p t then p t else 0)+
        (if r<d then U.card*(2*(Nat.card K:ℝ)^(d-r-1))*J else 0) := by
    intro z₁ z₂
    unfold indicator
    calc
      _ = ∑ t ∈ HighRankExcess.excessCarrier U
          (fun y => hitSpan a b y z₁ ⊔ hitSpan a b y z₂) r, p t := by
        convert HighRankExcess.target_event_eq U
          (fun y => hitSpan a b y z₁ ⊔ hitSpan a b y z₂) r p hsupp using 1
        congr!
      _ ≤ _ := HighRankExcess.target_excess_mass_sharp hdim hr U _ p hp J hJ
  apply (mean2_mono _ _ (fun z => ProductLaw.nonneg w hw z)
    (fun z => ProductLaw.nonneg w hw z) H).trans
  exact le_of_eq (mean2_const _ _ hnt hnt _)

theorem averaged_coverage (w : Ω → ℝ) (hw : ∀ z, 0 ≤ w z) (ht : ∑ z, w z=1)
    (p : Projectivization K V × Projectivization K (Module.Dual K V) → ℝ)
    (hp : ∀ t, 0 ≤ p t) (hpt : ∑ t, p t=1)
    (hincident : ∀ t, p t≠0 → t.2.rep t.1.rep=0)
    (U : Finset (Projectivization K V)) (hsupp : ∀ t, p t≠0 → t.1 ∈ U)
    (a : Ω → Module.Dual K V) (b : Ω → Projectivization K V)
    (h d r m T : ℕ) (hdim : Module.finrank K V=d+1) (hr : 2 ≤ r) (hrd : r ≤ d)
    (e : Fin r × Fin m ↪ Fin h) (M J : ℝ) (hM0 : 0 ≤ M) (hJ : 0 ≤ J)
    (hM : ∀ u, (∑ z ∈ univ.filter (fun z => b z=u), w z) ≤ M)
    (hT : (T:ℝ) ≤ (h:ℝ)/(10*(Nat.card K:ℝ))+1) :
    (∑ t, p t*mean2 (ProductLaw.weight w : (Fin h → Ω) → ℝ)
      (ProductLaw.weight w : (Fin h → Ω) → ℝ)
      (fun z₁ z₂ => indicator (¬Admitted a b z₁ z₂ r T t.1 t.2))) ≤
      (∑ t, p t*indicator
        ((∑ z ∈ univ.filter (fun z => a z t.1.rep=0), w z)<2/(5*(Nat.card K:ℝ))))+
      (r*(1-(2/(5*(Nat.card K:ℝ))-2*M*(Nat.card K:ℝ)^(r-2)))^m+
        Real.exp (1-(h:ℝ)/(10*(Nat.card K:ℝ))))+
      2*h*(∑ t, p t*conflictMass w a b t.1 t.2)+
      (∑ t ∈ U ×ˢ univ, if J < p t then p t else 0)+
      (if r<d then U.card*(2*(Nat.card K:ℝ)^(d-r-1))*J else 0) := by
  let G (t : Projectivization K V × Projectivization K (Module.Dual K V)) : Prop :=
    2/(5*(Nat.card K:ℝ)) ≤ ∑ z ∈ univ.filter (fun z => a z t.1.rep=0), w z
  let B : ℝ := r*(1-(2/(5*(Nat.card K:ℝ))-2*M*(Nat.card K:ℝ)^(r-2)))^m+
    Real.exp (1-(h:ℝ)/(10*(Nat.card K:ℝ)))
  let R : (Fin h → Ω) → ℝ := ProductLaw.weight w
  let X (t : Projectivization K V × Projectivization K (Module.Dual K V)) : ℝ :=
    mean2 R R (fun z₁ z₂ => indicator
      (r < Module.finrank K (hitSpan a b t.1 z₁ ⊔ hitSpan a b t.1 z₂ : Submodule K V) ∧
       hitSpan a b t.1 z₁ ⊔ hitSpan a b t.1 z₂ ≤ LinearMap.ker t.2.rep))
  let F (t : Projectivization K V × Projectivization K (Module.Dual K V)) : ℝ :=
    mean2 R R (fun z₁ z₂ => indicator (¬Admitted a b z₁ z₂ r T t.1 t.2))
  have hnt : ∑ z, R z=1 := by
    convert ProductLaw.total (ι := Fin h) w ht using 1
    congr!
  have hn : ∀ z, 0 ≤ R z := fun z => ProductLaw.nonneg w hw z
  have hX : ∀ t, 0 ≤ X t := fun t =>
    mean2_nonneg R R hn hn _ (fun _ _ => indicator_nonneg _)
  have hC : ∀ t : Projectivization K V × Projectivization K (Module.Dual K V), 0 ≤ conflictMass w a b t.1 t.2 := by
    intro t
    apply sum_nonneg
    intro z _
    exact mul_nonneg (hw z) (indicator_nonneg _)
  have hF : ∀ t, F t ≤ 1 := by
    intro t
    apply (mean2_mono R R hn hn (fun _ _ => indicator_le_one _)).trans
    exact le_of_eq (mean2_const R R hnt hnt 1)
  have hq : (2:ℝ) ≤ Nat.card K := by exact_mod_cast (Finite.one_lt_card : 1 < Nat.card K)
  have hH : 2/(5*(Nat.card K:ℝ)) ≤ 1 := by
    apply (div_le_one (by positivity)).mpr
    linarith
  have hB : 0 ≤ B := by
    dsimp [B]
    apply add_nonneg _ (Real.exp_pos _).le
    apply mul_nonneg (Nat.cast_nonneg r)
    apply pow_nonneg
    have hh : 0 ≤ 2*M*(Nat.card K:ℝ)^(r-2) := by positivity
    linarith
  have hh := average_with_exception p hp hpt G F
    (fun t => 2*h*conflictMass w a b t.1 t.2+X t) B hB
    (fun t => add_nonneg (mul_nonneg (by positivity) (hC t)) (hX t)) hF
    (by
      intro t hpt hG
      have H := fixed_query_bound w hw ht a b t.1 t.2 (hincident t hpt)
        h r m T e hr M hM0 hM hG hT
      dsimp [F, B, R, X]
      exact H.trans_eq (by ring))
  have he := excess_average w hw ht p hp U hsupp a b h d r hdim hrd J hJ
  have hsum : (∑ t, p t*(2*h*conflictMass w a b t.1 t.2+X t)) =
      2*h*(∑ t, p t*conflictMass w a b t.1 t.2)+∑ t, p t*X t := by
    simp_rw [mul_add, sum_add_distrib]
    congr 1
    rw [mul_sum]
    apply sum_congr rfl
    intro t _
    ring
  rw [hsum] at hh
  have herr : (∑ t, p t*indicator (¬G t)) =
      ∑ t, p t*indicator
        ((∑ z ∈ univ.filter (fun z => a z t.1.rep=0), w z)<2/(5*(Nat.card K:ℝ))) := by
    simp only [G, not_le]
  rw [herr] at hh
  dsimp [F, B, X, R] at hh
  linarith

end
end SharpLogRamsey.HighRankAveraged

namespace SharpLogRamsey.Incidence
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
section Projective
variable [Finite K] [FiniteDimensional K V]
variable [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]

theorem low_incidence_target_mass {n : ℕ} (hdim : Module.finrank K V = n+3)
    (w : Projectivization K V → ℝ) (hw : ∀ x, 0 ≤ w x) (ht : ∑ x, w x = 1)
    (M : ℝ) (hM : ∀ x, w x ≤ M)
    (v : Projectivization K (Module.Dual K V) → ℝ) (N : ℝ)
    (hN0 : 0 ≤ N) (hN : ∀ y, v y ≤ N) :
    (∑ y ∈ univ.filter (fun y => weightedIncidences SharpLogRamsey.Incidence.Incident w y <
      2/(5*(Nat.card K:ℝ))), v y) ≤ 100*(Nat.card K:ℝ)^(n+3)*M*N := by
  let q : ℝ := Nat.card K
  let u : ℝ := ∑ i ∈ range (n+2), q^i
  let p : ℝ := u/(∑ i ∈ range (n+3), q^i)
  let B := univ.filter (fun y => weightedIncidences SharpLogRamsey.Incidence.Incident w y < 2/(5*q))
  have hq : 2 ≤ q := by
    change (2:ℝ) ≤ Nat.card K
    exact_mod_cast (Finite.one_lt_card : 1 < Nat.card K)
  have hq0 : 0 < q := by linarith
  have hu : 1 ≤ u := by
    have hs := single_le_sum (f := fun i => q^i)
      (fun i _ => pow_nonneg hq0.le i) (show 0 ∈ range (n+2) by simp)
    simpa [u] using hs
  have hvpos : 0 < ∑ i ∈ range (n+3), q^i := by
    rw [geom_sum_succ]
    change 0 < q*u+1
    positivity
  have hp : 1/(2*q) ≤ p := by
    change 1/(2*q) ≤ u/(∑ i ∈ range (n+3), q^i)
    apply (div_le_div_iff₀ (by positivity) hvpos).mpr
    rw [geom_sum_succ]
    change 1*(q*u+1) ≤ u*(2*q)
    nlinarith
  have hnorm : (∑ x, w x^2) ≤ M := by
    calc
      _ ≤ ∑ x, M*w x := by
        apply sum_le_sum
        intro x _
        nlinarith [mul_le_mul_of_nonneg_right (hM x) (hw x)]
      _ = M := by rw [← mul_sum, ht, mul_one]
  have hvar := (projective_variance_le hdim w).trans
    (mul_le_mul_of_nonneg_left hnorm (show 0 ≤ q^(n+1) by positivity))
  change (∑ y, (weightedIncidences SharpLogRamsey.Incidence.Incident w y-p*(∑ x, w x))^2) ≤ q^(n+1)*M at hvar
  rw [ht, mul_one] at hvar
  have hc : (B.card:ℝ)*(1/(10*q))^2 ≤ q^(n+1)*M := by
    calc
      _ = ∑ _y ∈ B, (1/(10*q))^2 := by simp
      _ ≤ ∑ y ∈ B, (weightedIncidences SharpLogRamsey.Incidence.Incident w y-p)^2 := by
        apply sum_le_sum
        intro y hy
        have hb : weightedIncidences SharpLogRamsey.Incidence.Incident w y < 2/(5*q) := (mem_filter.mp hy).2
        have hg : 1/(10*q) ≤ p-weightedIncidences SharpLogRamsey.Incidence.Incident w y := by
          have he : 1/(2*q)-2/(5*q) = 1/(10*q) := by field_simp; ring
          linarith
        have hi : 0 ≤ 1/(10*q) := by positivity
        nlinarith
      _ ≤ ∑ y, (weightedIncidences SharpLogRamsey.Incidence.Incident w y-p)^2 := by
        apply sum_le_sum_of_subset_of_nonneg (subset_univ B)
        intro y _ _
        positivity
      _ ≤ _ := hvar
  have hmult := mul_le_mul_of_nonneg_right hc (show 0 ≤ 100*q^2 by positivity)
  have hcancel : (B.card:ℝ)*(1/(10*q))^2*(100*q^2) = B.card := by
    field_simp
    ring
  rw [hcancel] at hmult
  have he : q^(n+1)*M*(100*q^2) = 100*q^(n+3)*M := by
    rw [show n+3 = (n+1)+2 by omega, pow_add]
    ring
  rw [he] at hmult
  change (∑ y ∈ B, v y) ≤ _
  calc
    _ ≤ ∑ _y ∈ B, N := by apply sum_le_sum; intro y _; exact hN y
    _ = (B.card:ℝ)*N := by simp
    _ ≤ (100*q^(n+3)*M)*N := mul_le_mul_of_nonneg_right hmult hN0

end Projective
end SharpLogRamsey.Incidence
namespace SharpLogRamsey.ProjectiveDuality
open SharpLogRamsey.Incidence
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable [Finite K]
variable [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
local instance flat_JoinedHighRankAssembly_5 : Fintype (Projectivization K (Module.Dual K (Module.Dual K V))) :=
  Fintype.ofEquiv _ (bidual (K := K) (V := V))

theorem low_incidence_dual_mass {n : ℕ} (hdim : Module.finrank K V=n+3)
    (w : Projectivization K (Module.Dual K V) → ℝ)
    (hw : ∀ b, 0 ≤ w b) (ht : ∑ b, w b=1) (M : ℝ) (hM : ∀ b, w b ≤ M)
    (v : Projectivization K V → ℝ) (N : ℝ) (hN0 : 0 ≤ N) (hN : ∀ y, v y ≤ N) :
    (∑ y ∈ univ.filter (fun y => (∑ b, if SharpLogRamsey.Incidence.Incident y b then w b else 0)<
      2/(5*(Nat.card K:ℝ))), v y) ≤ 100*(Nat.card K:ℝ)^(n+3)*M*N := by
  have H := low_incidence_target_mass
    (show Module.finrank K (Module.Dual K V)=n+3 from Subspace.dual_finrank_eq.trans hdim)
    w hw ht M hM (fun y => v (bidual.symm y)) N hN0 (fun y => hN _)
  rw [sum_filter] at H ⊢
  have he : (∑ y : Projectivization K (Module.Dual K (Module.Dual K V)),
      if weightedIncidences SharpLogRamsey.Incidence.Incident w y < 2/(5*(Nat.card K:ℝ)) then v (bidual.symm y) else 0) =
      ∑ y : Projectivization K V,
        if (∑ b, if SharpLogRamsey.Incidence.Incident y b then w b else 0) < 2/(5*(Nat.card K:ℝ)) then v y else 0 := by
    rw [← (bidual (K := K) (V := V)).sum_comp]
    simp only [Equiv.symm_apply_apply, weightedIncidences, incident_bidual]
  rwa [he] at H
end
end SharpLogRamsey.ProjectiveDuality

namespace SharpLogRamsey.HighRankLowHit
open scoped BigOperators
open Finset Classical SharpLogRamsey.Incidence SharpLogRamsey.FiniteMarginals
noncomputable section
variable {K V Ω : Type*} [Field K] [AddCommGroup V] [Module K V]
    [Finite K] [FiniteDimensional K V] [Fintype Ω]
    [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]

omit [Finite K] [FiniteDimensional K V] [Fintype (Projectivization K V)] in
lemma hit_mass (w : Ω → ℝ) (a : Ω → Projectivization K (Module.Dual K V))
    (y : Projectivization K V) :
    (∑ z ∈ univ.filter (fun z => (a z).rep y.rep=0), w z) =
      ∑ b, if SharpLogRamsey.Incidence.Incident y b then marginal w a b else 0 := by
  have H := sum_marginal w a (fun b => if SharpLogRamsey.Incidence.Incident y b then 1 else 0)
  rw [sum_filter]
  calc
    _ = ∑ z, w z*(if SharpLogRamsey.Incidence.Incident y (a z) then 1 else 0) := by
      apply sum_congr rfl
      intro z _
      by_cases hz : (a z).rep y.rep=0 <;> simp [SharpLogRamsey.Incidence.Incident, hz]
    _ = ∑ b, marginal w a b*(if SharpLogRamsey.Incidence.Incident y b then 1 else 0) := H.symm
    _ = _ := by
      apply sum_congr rfl
      intro b _
      split_ifs <;> simp

theorem low_hit_mass {n : ℕ} (hdim : Module.finrank K V=n+3)
    (w : Ω → ℝ) (hw : ∀ z, 0 ≤ w z) (ht : ∑ z, w z=1)
    (a : Ω → Projectivization K (Module.Dual K V)) (M : ℝ)
    (hM : ∀ b, marginal w a b ≤ M)
    (p : Projectivization K V × Projectivization K (Module.Dual K V) → ℝ)
    (N : ℝ) (hN0 : 0 ≤ N) (hN : ∀ y, (∑ c, p (y,c)) ≤ N) :
    (∑ t, p t*(if (∑ z ∈ univ.filter (fun z => (a z).rep t.1.rep=0), w z)<
      2/(5*(Nat.card K:ℝ)) then 1 else 0)) ≤ 100*(Nat.card K:ℝ)^(n+3)*M*N := by
  have H := ProjectiveDuality.low_incidence_dual_mass hdim (marginal w a)
    (marginal_nonneg w hw a) (by rw [marginal_total, ht]) M hM
    (fun y => ∑ c, p (y,c)) N hN0 hN
  rw [sum_filter] at H
  simp_rw [Fintype.sum_prod_type, hit_mass]
  convert H using 1
  apply sum_congr rfl
  intro y _
  rw [← sum_mul]
  split_ifs <;> simp
end
end SharpLogRamsey.HighRankLowHit

namespace SharpLogRamsey.HighRankBudgets
open Filter Real
open scoped Topology BigOperators
noncomputable section

def beta (η : ℝ) : ℝ := η/10000000
def scaleK (σ η D : ℝ) : ℝ := D*σ^(3*beta η)

lemma eventually_monomial_le_linear (C a ε : ℝ) (ha : a < 1) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, C*x^a ≤ ε*x := by
  have ht : Tendsto (fun x : ℝ => C*x^(a-1)) atTop (𝓝 0) := by
    convert (tendsto_rpow_neg_atTop (sub_pos.mpr ha)).const_mul C using 1 <;> simp
  filter_upwards [ht.eventually (gt_mem_nhds hε), eventually_gt_atTop (0 : ℝ)] with x hx hx0
  calc
    _ = (C*x^(a-1))*x := by
      have hp : x^(a-1)*x = x^a := by
        calc
          _ = x^(a-1)*x^(1 : ℝ) := by rw [Real.rpow_one]
          _ = _ := by rw [← Real.rpow_add hx0]; congr 1; ring
      rw [mul_assoc, hp]
    _ ≤ ε*x := mul_le_mul_of_nonneg_right hx.le hx0.le

lemma K_upper {σ η D : ℝ} (hσ : 0<σ) (hD : D ≤ σ^(1-η/2)) :
    scaleK σ η D ≤ σ^(1-η/2+3*beta η) := by
  unfold scaleK
  calc
    _ ≤ σ^(1-η/2)*σ^(3*beta η) := mul_le_mul_of_nonneg_right hD (by positivity)
    _ = _ := (Real.rpow_add hσ _ _).symm

lemma eventually_K_linear {η : ℝ} (hη : 0<η) (c ε : ℝ) (hc : 0≤c) (hε : 0<ε) :
    ∀ᶠ σ : ℝ in atTop, ∀ D : ℝ, D ≤ σ^(1-η/2) → c*scaleK σ η D ≤ ε*σ := by
  have he : 1-η/2+3*beta η < 1 := by unfold beta; linarith
  filter_upwards [eventually_monomial_le_linear c (1-η/2+3*beta η) ε he hε,
    eventually_gt_atTop (0:ℝ)] with σ hh hσ D hD
  exact (mul_le_mul_of_nonneg_left (K_upper hσ hD) hc).trans hh

theorem eventually_exp_K_over_q {η : ℝ} (hη : 0<η) (C a ε : ℝ)
    (hC : 0≤C) (ha : 0≤a) (hε : 0<ε) :
    ∀ᶠ σ : ℝ in atTop, ∀ D : ℝ, D ≤ σ^(1-η/2) →
      C*Real.exp (a*scaleK σ η D)/Real.exp σ < ε := by
  have ht : Tendsto (fun σ : ℝ => C*Real.exp (-(σ/2))) atTop (𝓝 0) := by
    have hneg : Tendsto (fun σ : ℝ => -(σ/2)) atTop atBot :=
      tendsto_neg_atTop_atBot.comp (tendsto_id.atTop_div_const (by norm_num : (0:ℝ)<2))
    simpa using (Real.tendsto_exp_atBot.comp hneg).const_mul C
  filter_upwards [eventually_K_linear hη a (1/2) ha (by norm_num),
    ht.eventually (gt_mem_nhds hε)] with σ hK hx D hD
  calc
    _ = C*Real.exp (a*scaleK σ η D-σ) := by rw [Real.exp_sub]; ring
    _ ≤ C*Real.exp (-(σ/2)) := by
      apply mul_le_mul_of_nonneg_left _ hC
      apply Real.exp_le_exp.mpr
      linarith [hK D hD]
    _ < ε := hx

lemma row_size {q x : ℝ} (hq : 1≤q) (hx : 1≤x) :
    q*x ≤ (⌈q*x⌉₊:ℝ) ∧ (⌈q*x⌉₊:ℝ) ≤ 2*q*x := by
  have hqx : 1≤q*x := by nlinarith
  exact ⟨Nat.le_ceil _, (Nat.ceil_lt_add_one (by positivity)).le.trans (by linarith)⟩

lemma block_size {h d : ℕ} (hd : 0<d) (hhd : 2*d ≤ h) :
    (h:ℝ)/(2*d) ≤ (h/d:ℕ) := by
  have he := Nat.mod_add_div h d
  have hm := Nat.mod_lt h hd
  have hq : 2 ≤ h/d := (Nat.le_div_iff_mul_le hd).mpr hhd
  have hb : h ≤ 2*d*(h/d) := by nlinarith
  apply (div_le_iff₀ (by positivity : (0:ℝ)<2*d)).mpr
  exact_mod_cast (show h ≤ h/d*(2*d) by nlinarith)

lemma block_embedding (h d r : ℕ) (hr : r ≤ d) : Nonempty (Fin r × Fin (h/d) ↪ Fin h) := by
  apply Function.Embedding.nonempty_of_card_le
  simp only [Fintype.card_prod, Fintype.card_fin]
  exact (Nat.mul_le_mul_right (h/d) hr).trans (Nat.mul_div_le h d)

theorem growth_tail {q M : ℝ} {r d h : ℕ} (hq : 2≤q) (hM : 0≤M)
    (hr : r≤d) (hd : 0<d) (hhd : 2*d≤h)
    (hescape : 2*M*q^(r-2) ≤ 1/(10*q)) :
    (r:ℝ)*(1-(2/(5*q)-2*M*q^(r-2)))^(h/d) ≤
      d*Real.exp (-3*(h:ℝ)/(20*d*q)) := by
  have hq0 : 0<q := by linarith
  have hb0 : 0 ≤ 1-(2/(5*q)-2*M*q^(r-2)) := by
    have hh : 2/(5*q) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
    have hp : 0 ≤ 2*M*q^(r-2) := by positivity
    linarith
  have heq : 2/(5*q)-1/(10*q)=3/(10*q) := by field_simp; ring
  have hh : 1-(2/(5*q)-2*M*q^(r-2)) ≤ Real.exp (-(3/(10*q))) := by
    have H := Real.add_one_le_exp (-(3/(10*q)))
    linarith
  have hm := block_size hd hhd
  have hex : -(3/(10*q))*(↑(h/d):ℝ) ≤ -3*(h:ℝ)/(20*d*q) := by
    have H := mul_le_mul_of_nonneg_left hm (show 0≤3/(10*q) by positivity)
    have he : 3/(10*q)*((h:ℝ)/(2*d)) = 3*h/(20*d*q) := by field_simp; ring
    rw [he] at H
    simpa only [neg_mul, neg_div] using neg_le_neg H
  calc
    _ ≤ (r:ℝ)*(Real.exp (-(3/(10*q))))^(h/d) := by gcongr
    _ = (r:ℝ)*Real.exp (-(3/(10*q))*(h/d:ℕ)) := by rw [←Real.exp_nat_mul]; congr 2; ring
    _ ≤ (r:ℝ)*Real.exp (-3*(h:ℝ)/(20*d*q)) := by gcongr
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hr) (Real.exp_nonneg _)

end
end SharpLogRamsey.HighRankBudgets
end

end OAI
