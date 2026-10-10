import OAI.Probability.TraceReconstruction.SourceOracle

namespace OAI

/-!
# InitialOracle

Actual initial scores and anchors, count partitions and typicality, clipped metadata, common decoding, sharp hidden-count energy, tails, and budget caps.
-/

open scoped ENNReal
noncomputable section

open Filter
open scoped Topology

noncomputable section
namespace TraceReconstruction
open scoped Classical
open FiniteLaw

def initialMomentRatio (u m : ℕ) (q w : ℝ) : ℝ :=
  w^2*(3*rankSchurConstant/q)*Real.sqrt ((u:ℝ)/m)

def initialSignedBudget (u m l R s : ℕ) (π : IntSeries) (θ q w : ℝ) : ℝ :=
  (∑r∈Finset.range R,w^(2*r)*signedInitialDegreeBound u m r s π θ l)+
    4*(initialMomentRatio u m q w)^R/(1-initialMomentRatio u m q w)

theorem initialSignedBudget_nonneg (u m l R s : ℕ) (π : IntSeries) (θ q w : ℝ)
    (hq : 0 ≤ q) (ha : initialMomentRatio u m q w < 1) :
    0 ≤ initialSignedBudget u m l R s π θ q w := by
  apply add_nonneg
  · exact Finset.sum_nonneg (fun r _ => mul_nonneg (by rw [pow_mul]; positivity)
      (signedInitialDegreeBound_nonneg _ _ _ _ _ _ _))
  · apply div_nonneg _ (sub_nonneg.mpr ha.le)
    exact mul_nonneg (by norm_num) (pow_nonneg (by unfold initialMomentRatio; positivity [rankSchurConstant_pos]) _)

/-- The signed score numerator in the *actual conditional mark-list laws*,
 with the entire finite cancellation energy and geometric tail retained. -/
theorem initial_signed_moment {u m l R : ℕ} (hu : 0 < u) (hm : 128 ≤ m)
    (hum : u ≤ m) (hR : 0 < R) (hl : l ≤ u*m) (off : Fin m)
    (hi : 1 ≤ off.val ∧ off.val+1 < m) (hoff : |(off.val:ℝ)-(m:ℝ)/2| ≤ 2)
    (hsafe : SafeTaggedTuple (periodSlot (u:=u) (fun _ => off)))
    (π : IntSeries) (hπ : ∀X,0 ≤ π.coeff X) (hπsum : ∑X∈π.coeff.support,π.coeff X=1)
    (s k : ℕ) (hcentral : CentralMotifSupport u s π) (hk : 1 ≤ k)
    {q θ w : ℝ} (hq : q∈Set.Ioc 0 (1/2:ℝ))
    (hθ : θ∈Set.Icc (1-q^2) (1-q^2/4))
    (hmean : ((u*m:ℕ):ℝ)*θ=l) (hv : 1 ≤ ((u*m:ℕ):ℝ)*θ*(1-θ))
    (hM : ((2*(2^s):ℕ):ℝ) < (u:ℝ)/(3*(R+1:ℝ)))
    (hw : w=((6*(2*k:ℕ):ℝ)*(2/q))) (ha : initialMomentRatio u m q w < 1) :
    ((primitiveMarkLaw q ⟨hq.1,lt_of_le_of_lt hq.2 (by norm_num)⟩ false).product l).evenMomentSq
      (fun x => initialMotifDensity hl off hsafe π s 1 q x-initialMotifDensity hl off hsafe π s (-1) q x) k  ≤ 
        initialSignedBudget u m l R s π θ q w := by
  have hq' : q∈Set.Ioo 0 1 := ⟨hq.1,lt_of_le_of_lt hq.2 (by norm_num)⟩
  have he : (fun x => initialMotifDensity hl off hsafe π s 1 q x-initialMotifDensity hl off hsafe π s (-1) q x)=
      multilinear (fun σ => mixedMotifCoefficient hl off hsafe π s 1 σ-mixedMotifCoefficient hl off hsafe π s (-1) σ)
        (primitiveScore q) := by funext x; exact (multilinear_sub _ _ _ _).symm
  rw [he]
  apply (multilinear_moment_sq_scaled (primitiveMarkLaw q hq' false) (primitiveScore q) k hk
    (primitive_score_centered hq') (div_pos (by norm_num) hq.1) (primitive_score_evenMoment hq' k) l _).trans
  rw [←hw]
  exact signed_initial_full_energy hu hm hum hR hl off hi hoff hsafe π hπ hπsum s hcentral hq hθ hmean hv hM
    (by rw [hw]; positivity [hq.1]) ha

/-- Quantitative normalized common clipping of the level-zero conditional
 pair. This theorem has only the literal count/geometric inequalities of the
 initial construction, not a signed-density or oracle conclusion premise. -/
theorem initial_conditional_clipped_exists {u m l R : ℕ} (hu : 0 < u) (hm : 128 ≤ m)
    (hum : u ≤ m) (hR : 0 < R) (hl : l ≤ u*m) (off : Fin m)
    (hi : 1 ≤ off.val ∧ off.val+1 < m) (hoff : |(off.val:ℝ)-(m:ℝ)/2| ≤ 2)
    (hsafe : SafeTaggedTuple (periodSlot (u:=u) (fun _ => off)))
    (π : IntSeries) (hπ : ∀X,0 ≤ π.coeff X) (hπsum : ∑X∈π.coeff.support,π.coeff X=1)
    (s k : ℕ) (hcentral : CentralMotifSupport u s π) (hk : 1 ≤ k)
    {q θ w : ℝ} (hq : q∈Set.Ioc 0 (1/2:ℝ))
    (hθ : θ∈Set.Icc (1-q^2) (1-q^2/4))
    (hmean : ((u*m:ℕ):ℝ)*θ=l) (hv : 1 ≤ ((u*m:ℕ):ℝ)*θ*(1-θ))
    (hM : ((2*(2^s):ℕ):ℝ) < (u:ℝ)/(3*(R+1:ℝ)))
    (hw : w=((6*(2*k:ℕ):ℝ)*(2/q))) (hscale : initialMomentRatio u m q w ≤ 1/2)
    (hclip : Real.sqrt (6*(4*(initialMomentRatio u m q w/(1-initialMomentRatio u m q w)))^k) ≤ 1/2) :
    Nonempty (ClippedOracle
      (conditionalMotifLaw hl off hsafe ⟨hq.1,lt_of_le_of_lt hq.2 (by norm_num)⟩ π hπ hπsum s (-1))
      (conditionalMotifLaw hl off hsafe ⟨hq.1,lt_of_le_of_lt hq.2 (by norm_num)⟩ π hπ hπsum s 1) k
      (Real.sqrt (6*(4*(initialMomentRatio u m q w/(1-initialMomentRatio u m q w)))^k))
      (64*initialSignedBudget u m l R s π θ q w)) := by
  have hq' : q∈Set.Ioo 0 1 := ⟨hq.1,lt_of_le_of_lt hq.2 (by norm_num)⟩
  let A := (primitiveMarkLaw q hq' false).product l
  let f := initialMotifDensity hl off hsafe π s (-1) q
  let g := initialMotifDensity hl off hsafe π s 1 q
  let U := initialMomentRatio u m q w/(1-initialMomentRatio u m q w)
  have ha : initialMomentRatio u m q w < 1 := by linarith
  have hz : 0 ≤ initialMomentRatio u m q w := by unfold initialMomentRatio; positivity [rankSchurConstant_pos,hq.1]
  have hU : 0 ≤ U := div_nonneg hz (sub_nonneg.mpr ha.le)
  have hU1 : U ≤ 1 := (div_le_iff₀ (sub_pos.mpr ha)).mpr (by linarith)
  have hmom (τ : ℝ) : A.expect (fun x => |initialMotifDensity hl off hsafe π s τ q x-1|^(2*k)) ≤ U^k :=
    A.expect_even_pow_le_of_moment _ k hk (initial_centered_moment hl (by omega) hum off hi hoff hsafe π hπ hπsum s k hk τ hq hθ hmean hv hw ha)
  have hV := initialSignedBudget_nonneg u m l R s π θ q w hq.1.le ha
  have hsig := A.expect_even_pow_le_of_moment _ k hk
    (initial_signed_moment hu hm hum hR hl off hi hoff hsafe π hπ hπsum s k hcentral hk hq hθ hmean hv hM hw ha)
  rw [initialMotifLaw_withDensity hl off hsafe π hπ hπsum s (-1) hq',
    initialMotifLaw_withDensity hl off hsafe π hπ hπsum s 1 hq']
  have H := A.exists_clippedOracle f g
    (initialMotifDensity_nonneg hl off hsafe π hπ hπsum s (-1) hq')
    (initialMotifDensity_nonneg hl off hsafe π hπ hπsum s 1 hq')
    (initialMotifDensity_mean hl off hsafe π hπ hπsum s (-1) hq')
    (initialMotifDensity_mean hl off hsafe π hπ hπsum s 1 hq')
    Finset.univ 0 (by simp [eventMass]) (by simp [eventMass]) k hk U hU hU1 (hmom (-1)) (hmom 1)
    (initialSignedBudget u m l R s π θ q w) hV (by simpa only [Finset.mem_univ,ite_true] using hsig)
    (by simpa only [zero_add] using hclip)
  simpa only [zero_add] using H

end TraceReconstruction

noncomputable section
namespace TraceReconstruction
open scoped Classical
namespace FiniteLaw
variable {α : Type*} [Fintype α]

theorem evenMomentSq_le_of_expect (P : FiniteLaw α) (F : α → ℝ) (k : ℕ) (hk : 1≤k)
    {V : ℝ} (hV : 0≤V) (h : P.expect (fun a => |F a|^(2*k))≤V^k) :
    P.evenMomentSq F k≤V := by
  have H := Real.rpow_le_rpow (P.expect_nonneg _ (fun _ => by positivity)) h (by positivity : 0≤(k:ℝ)⁻¹)
  rw [Real.pow_rpow_inv_natCast hV (by omega)] at H
  simpa only [FiniteLaw.evenMomentSq,one_div] using H

theorem tv_sigma_eq {ι : Type*} [Fintype ι] {β : ι → Type*} [∀i,Fintype (β i)]
    (M : FiniteLaw ι) (P Q : ∀i,FiniteLaw (β i)) :
    (M.sigma P).tv (M.sigma Q)=M.expect (fun i => (P i).tv (Q i)) := by
  simp only [tv,sigma,expect,Fintype.sum_sigma,←mul_sub,abs_mul,abs_of_nonneg (M.nonneg _)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [←Finset.mul_sum]
  ring

end FiniteLaw
namespace ClippedOracle
variable {α : Type*} [Fintype α] {P Q : FiniteLaw α} {k : ℕ} {e V E W : ℝ}

def weaken (C : ClippedOracle P Q k e V) (he : e≤E) (hV : V≤W) : ClippedOracle P Q k E W where
  first := C.first
  second := C.second
  score := C.score
  density := C.density
  likelihood_nonneg := C.likelihood_nonneg
  centered := C.centered
  moment := C.moment.trans hV
  first_tv := C.first_tv.trans he
  second_tv := C.second_tv.trans he

def trivial (P Q : FiniteLaw α) (k : ℕ) (hk : 1≤k) : ClippedOracle P Q k 1 0 where
  first := P
  second := P
  score := fun _ => 0
  density := fun _ => by ring
  likelihood_nonneg := fun _ => by norm_num
  centered := by simp [FiniteLaw.expect]
  moment := by
    apply P.evenMomentSq_le_of_expect _ k hk (by norm_num)
    simp [FiniteLaw.expect,zero_pow (by omega : 2*k≠0)]
  first_tv := by simp [FiniteLaw.tv]
  second_tv := FiniteLaw.tv_le_one _ _

/-- Reported metadata is retained, so the squared moment of a normalized
 score assembles without a mixing penalty. No conditioning of the original
 latent metadata distribution occurs. -/
def sigma {ι : Type*} [Fintype ι] {β : ι → Type*} [∀i,Fintype (β i)]
    (M : FiniteLaw ι) (P Q : ∀i,FiniteLaw (β i)) (e : ι → ℝ)
    (k : ℕ) (hk : 1≤k) (V : ℝ) (hV : 0≤V)
    (C : ∀i,ClippedOracle (P i) (Q i) k (e i) V) :
    ClippedOracle (M.sigma P) (M.sigma Q) k (M.expect e) V where
  first := M.sigma (fun i => (C i).first)
  second := M.sigma (fun i => (C i).second)
  score := fun a => (C a.1).score a.2
  density := fun a => by dsimp only [FiniteLaw.sigma]; rw [(C a.1).density]; ring
  likelihood_nonneg := fun a => (C a.1).likelihood_nonneg a.2
  centered := by
    rw [FiniteLaw.expect_sigma]
    simp_rw [(C _).centered]
    simp [FiniteLaw.expect]
  moment := by
    apply FiniteLaw.evenMomentSq_le_of_expect _ _ k hk hV
    rw [FiniteLaw.expect_sigma]
    calc
      _ ≤ M.expect (fun _ => V^k) := M.expect_mono (fun i =>
        (C i).first.expect_even_pow_le_of_moment _ k hk (C i).moment)
      _ = _ := M.expect_const _
  first_tv := by
    rw [FiniteLaw.tv_sigma_eq]
    exact M.expect_mono (fun i => (C i).first_tv)
  second_tv := by
    rw [FiniteLaw.tv_sigma_eq]
    exact M.expect_mono (fun i => (C i).second_tv)

/-- Replace bad conditional observations by a common law rather than making
 the original metadata law conditional on typicality. The exact cost is
 the true metadata failure mass plus the good conditional clipping cost. -/
theorem assemble_good {ι : Type*} [Fintype ι] {β : ι → Type*} [∀i,Fintype (β i)]
    (M : FiniteLaw ι) (P Q : ∀i,FiniteLaw (β i)) (Good : ι → Prop)
    (k : ℕ) (hk : 1≤k) (e V : ℝ) (he : 0≤e) (hV : 0≤V)
    (C : ∀i,Good i → Nonempty (ClippedOracle (P i) (Q i) k e V)) :
    Nonempty (ClippedOracle (M.sigma P) (M.sigma Q) k
      (e+M.expect (fun i => if Good i then 0 else 1)) V) := by
  let err := fun i => if Good i then e else 1
  have hi (i) : Nonempty (ClippedOracle (P i) (Q i) k (err i) V) := by
    by_cases h : Good i
    · simpa only [err,ite_eq_left h] using C i h
    · exact ⟨(trivial (P i) (Q i) k hk).weaken (by simp [err,h]) hV⟩
  let D := sigma M P Q err k hk V hV (fun i => Classical.choice (hi i))
  refine ⟨D.weaken ?_ le_rfl⟩
  calc
    M.expect err ≤ M.expect (fun i => e+(if Good i then 0 else 1)) := M.expect_mono (fun i => by
      dsimp only [err]; split_ifs <;> linarith)
    _ = _ := by rw [M.expect_add,M.expect_const]

end ClippedOracle
end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open scoped Classical
open FiniteLaw

theorem translated_fair_eval (g : ℕ) (c : ℤ) (F : ℤ → ℝ) :
    (∑X∈(translateSeries c (fairSeries g)).coeff.support,
      (translateSeries c (fairSeries g)).coeff X*F X)=
    ∑k∈Finset.range (g+1),fairBinomial g k*F (c+k) := by
  have H := congrArg (fun p : IntSeries => Finsupp.linearCombination ℝ F p.coeff)
    (congrArg (translateSeries c) (fairSeries_sum g))
  simp only [translateSeries,Finset.mul_sum,AddMonoidAlgebra.single_mul_single,one_mul,
    AddMonoidAlgebra.coeff_sum,AddMonoidAlgebra.coeff_single,map_sum,
    Finsupp.linearCombination_single,smul_eq_mul] at H
  exact H

/-- The literal initial anchor after conditioning the paired side outputs. -/
def posteriorAnchorSeries {ι : Type*} [Fintype ι] (c : ℤ) (d : ι → Option Bool) : IntSeries :=
  translateSeries (c-(∑i,(visibleOnes (d i):ℤ))-(∑i,hiddenTrial (d i)))
    (fairSeries (∑i,hiddenTrial (d i)))

theorem posterior_anchor_average {ι : Type*} [Fintype ι]
    (c : ℤ) (d : ι → Option Bool) (F : ℤ → ℝ) :
    (∑b : ι → Bool, (∏i,(flagPosterior (d i)).mass (b i))*
      F (c-∑i,(bitIndex (b i):ℤ)))=
    ∑X∈(posteriorAnchorSeries c d).coeff.support,(posteriorAnchorSeries c d).coeff X*F X := by
  rw [posterior_count_average_reflected d (fun z => F (c-z)),posteriorAnchorSeries,translated_fair_eval]
  apply Finset.sum_congr rfl
  intro k _
  congr 2
  ring

theorem posteriorAnchorSeries_nonneg {ι : Type*} [Fintype ι]
    (c : ℤ) (d : ι → Option Bool) (X : ℤ) : 0 ≤ (posteriorAnchorSeries c d).coeff X :=
  translated_binomial_nonneg _ _ _

theorem posteriorAnchorSeries_total {ι : Type*} [Fintype ι]
    (c : ℤ) (d : ι → Option Bool) :
    ∑X∈(posteriorAnchorSeries c d).coeff.support,(posteriorAnchorSeries c d).coeff X=1 := by
  have H := posterior_anchor_average c d (fun _ => 1)
  simp only [mul_one] at H
  rw [←H]
  exact (FiniteLaw.indexedProduct (fun i => flagPosterior (d i))).total

theorem posteriorAnchorSeries_support {ι : Type*} [Fintype ι]
    (c : ℤ) (d : ι → Option Bool) (X : ℤ) (hX : X∈(posteriorAnchorSeries c d).coeff.support) :
    c-Fintype.card ι ≤ X ∧ X ≤ c := by
  have H := translated_binomial_support (∑i,hiddenTrial (d i))
    (c-(∑i,(visibleOnes (d i):ℤ))-(∑i,hiddenTrial (d i))) X
    (Finsupp.mem_support_iff.mp hX)
  have hz : 0 ≤ ∑i,(visibleOnes (d i):ℤ) := Finset.sum_nonneg (fun _ _ => by positivity)
  have hh : (∑i,(visibleOnes (d i):ℤ))+(∑i,hiddenTrial (d i)) ≤ Fintype.card ι := by
    rw [Nat.cast_sum,←Finset.sum_add_distrib]
    calc
      _ ≤ ∑_i : ι,(1:ℤ) := Finset.sum_le_sum (fun i _ => by
        cases h:d i with
        | none => simp [visibleOnes,hiddenTrial]
        | some b => cases b <;> simp [visibleOnes,hiddenTrial])
      _ = _ := by simp
  omega

theorem posteriorAnchorSeries_central {ι : Type*} [Fintype ι]
    (u s : ℕ) (c : ℤ) (d : ι → Option Bool)
    (hleft : (u:ℝ)/3 ≤ 2*((c:ℝ)-Fintype.card ι)+1)
    (hright : (u:ℝ)/3 ≤ 2*u-(2*((c:ℝ)+(2:ℝ)^s)+1)) :
    CentralMotifSupport u s (posteriorAnchorSeries c d) := by
  intro X hX
  have H := posteriorAnchorSeries_support c d X hX
  have H₁ : (c:ℝ)-Fintype.card ι ≤ X := by exact_mod_cast H.1
  have H₂ : (X:ℝ) ≤ c := by exact_mod_cast H.2
  constructor <;> linarith

namespace PairedMechanisms
variable {Side α : Type*} [Fintype Side] [Fintype α] {J : ℕ}

def emissionOracle (M : PairedMechanisms Side J) (K : (Fin J → Bool) → FiniteLaw α) :
    FiniteLaw (Reports Side J × α) :=
  M.reports.joint (fun z => (orientationsGiven z).mixture K)

/-- Bayes factorization is valid for arbitrary conditional finite emissions,
 including the dependent-length initial primitive-mark list. -/
theorem emission_factorization (M : PairedMechanisms Side J) (K : (Fin J → Bool) → FiniteLaw α) :
    (fairOrientations J).mixture (fun b => (M.reportsGiven b).prod (K b))=M.emissionOracle K := by
  apply FiniteLaw.ext
  funext zx
  rcases zx with ⟨z,x⟩
  change (∑b,(∏i : Fin J,(1/2:ℝ))*
    ((∏i,FiniteLaw.pairedFlagMass (M.first i) (M.second i) (M.common i)
      (M.hiddenWeight i) (b i) (z i))*(K b).mass x))=
    (∏i,FiniteLaw.pairedReportMass (M.first i) (M.second i) (M.common i)
      (M.hiddenWeight i) (z i))*(∑b,(∏i,(flagPosterior (z i).1).mass (b i))*(K b).mass x)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [←mul_assoc,←Finset.prod_mul_distrib,FiniteLaw.pairedFlags_product_bayes,mul_assoc]

end PairedMechanisms

theorem conditionalMotifLaw_posterior {u m l J : ℕ} (hl : l ≤ u*m) (off : Fin m)
    (hsafe : SafeTaggedTuple (periodSlot (u:=u) (fun _ => off)))
    {q : ℝ} (hq : q∈Set.Ioo 0 1) (c : ℤ) (d : Fin J → Option Bool) (s : ℕ) (τ : ℝ) :
    (FiniteLaw.coordinateProduct (fun i => flagPosterior (d i))).mixture
      (fun b => conditionalPrimitiveLaw hl q hq
        (defectTypes (signedPeriodDefects off hsafe s (c-∑i,(bitIndex (b i):ℤ)) τ)))=
    conditionalMotifLaw hl off hsafe hq (posteriorAnchorSeries c d)
      (posteriorAnchorSeries_nonneg c d) (posteriorAnchorSeries_total c d) s τ := by
  apply FiniteLaw.ext
  funext x
  change (∑b : Fin J → Bool,(∏i : Fin J,(flagPosterior (d i)).mass (b i))*
    (conditionalPrimitiveLaw hl q hq (defectTypes (signedPeriodDefects off hsafe s
      (c-∑i,(bitIndex (b i):ℤ)) τ))).mass x)=_
  classical
  have H := posterior_anchor_average c d (fun X =>
    (conditionalPrimitiveLaw hl q hq (defectTypes (signedPeriodDefects off hsafe s X τ))).mass x)
  calc
    _ = ∑X∈(posteriorAnchorSeries c d).coeff.support,
        (posteriorAnchorSeries c d).coeff X*
          (conditionalPrimitiveLaw hl q hq (defectTypes (signedPeriodDefects off hsafe s X τ))).mass x := by
      convert H using 1
      congr 1
      ext b
      simp
    _ = _ := (Finset.sum_coe_sort _ _).symm


/-- Initial observations retain the central count with its original binomial law. -/
def countedMotifLaw {u m : ℕ} (off : Fin m)
    (hsafe : SafeTaggedTuple (periodSlot (u:=u) (fun _ => off)))
    {q : ℝ} (hq : q∈Set.Ioo 0 1) (π : IntSeries) (hπ : ∀X,0 ≤ π.coeff X)
    (hπsum : ∑X∈π.coeff.support,π.coeff X=1) (s : ℕ) (τ : ℝ) :
    FiniteLaw (BoundedMarks (u*m)) :=
  (boundedCountLaw (le_refl (u*m)) (1-primitiveErasure q) (primitiveRetention_mem hq)).sigma
    (fun l => conditionalMotifLaw (by omega) off hsafe hq π hπ hπsum s τ)

theorem countedMotifLaw_posterior {u m J : ℕ} (off : Fin m)
    (hsafe : SafeTaggedTuple (periodSlot (u:=u) (fun _ => off)))
    {q : ℝ} (hq : q∈Set.Ioo 0 1) (c : ℤ) (d : Fin J → Option Bool) (s : ℕ) (τ : ℝ) :
    (FiniteLaw.coordinateProduct (fun i => flagPosterior (d i))).mixture
      (fun b => countedPrimitiveLaw (le_refl (u*m)) hq
        (defectTypes (signedPeriodDefects off hsafe s (c-∑i,(bitIndex (b i):ℤ)) τ)))=
    countedMotifLaw off hsafe hq (posteriorAnchorSeries c d)
      (posteriorAnchorSeries_nonneg c d) (posteriorAnchorSeries_total c d) s τ := by
  apply FiniteLaw.ext
  funext x
  rcases x with ⟨l,x⟩
  have hl : l.val ≤ u*m := by omega
  have H := congrArg (fun P : FiniteLaw (Fin l.val → PrimitiveMark) => P.mass x)
    (conditionalMotifLaw_posterior hl off hsafe hq c d s τ)
  change (∑b, _ * ((boundedCountLaw _ _ _).mass l *
    (boundedConditionalPrimitiveLaw hq _ l).mass x))=_
  simp only [boundedConditionalPrimitiveLaw,dite_eq_left hl]
  change _ = (boundedCountLaw _ _ _).mass l * _
  rw [←H]
  simp only [FiniteLaw.mixture,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  ring


end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open scoped Classical

/-- The actual displaced primitive slot in a period. -/
def motifOffset {m : ℕ} (off : Fin m) (hi : 1 ≤ off.val ∧ off.val+1 < m)
    (s : ℕ) (X : ℤ) (τ : ℝ) (j : ℤ) : Fin m :=
  ⟨off.val+(motifShift (motifIndicator s (j-X)) ((prouhetSeries s).coeff (j-X)) τ).val-1, by
    have H := (motifShift (motifIndicator s (j-X)) ((prouhetSeries s).coeff (j-X)) τ).isLt
    omega⟩

theorem signedPeriodDefects_periodSlot {u m : ℕ} (off : Fin m)
    (hi : 1 ≤ off.val ∧ off.val+1 < m)
    (hsafe : SafeTaggedTuple (periodSlot (u:=u) (fun _ => off)))
    (s : ℕ) (X : ℤ) (τ : ℝ) :
    signedPeriodDefects off hsafe s X τ =
      periodSlot (fun j => motifOffset off hi s X τ j.val) := by
  funext j
  apply Fin.ext
  simp only [signedPeriodDefects,shiftedTag,periodSlot,motifOffset]
  omega

def motifPeriodWord {m : ℕ} (off : Fin m) (hi : 1 ≤ off.val ∧ off.val+1 < m)
    (u s : ℕ) (X : ℤ) (τ : ℝ) : List Bool :=
  periodString m u (fun j => motifOffset off hi s X τ j.val)

theorem signed_primitive_word {u m : ℕ} (off : Fin m)
    (hi : 1 ≤ off.val ∧ off.val+1 < m)
    (hsafe : SafeTaggedTuple (periodSlot (u:=u) (fun _ => off)))
    (s : ℕ) (X : ℤ) (τ : ℝ) :
    (((List.ofFn (defectTypes (signedPeriodDefects off hsafe s X τ))).map primitiveBlock).flatten)=
    motifPeriodWord off hi u s X τ := by
  rw [signedPeriodDefects_periodSlot off hi,periodic_primitive_word]
  rfl

theorem motifOffset_outside {m : ℕ} (off : Fin m) (hi : 1 ≤ off.val ∧ off.val+1 < m)
    (s : ℕ) (X : ℤ) (τ : ℝ) (j : ℤ) (hj : j<X ∨ X+(2^s:ℕ) ≤ j) :
    motifOffset off hi s X τ j=off := by
  apply Fin.ext
  have h : ¬(0 ≤ j-X ∧ j-X<(2^s:ℕ)) := by omega
  simp only [motifOffset,motifIndicator,ite_eq_right h,motifShift,ite_true]
  norm_num

theorem motifOffset_translate {m : ℕ} (off : Fin m) (hi : 1 ≤ off.val ∧ off.val+1 < m)
    (s : ℕ) (X t : ℤ) (τ : ℝ) (j : ℤ) :
    motifOffset off hi s X τ (t+j)=motifOffset off hi s (X-t) τ j := by
  have h : t+j-X=j-(X-t) := by ring
  simp only [motifOffset,h]

theorem periodString_three {m : ℕ} (n k z : ℕ) (off : Fin (n+k+z) → Fin m) :
    periodString m (n+k+z) off =
      periodString m n (fun i => off ⟨i.val,by omega⟩) ++
      periodString m k (fun i => off ⟨n+i.val,by omega⟩) ++
      periodString m z (fun i => off ⟨n+k+i.val,by omega⟩) := by
  simp only [periodString,List.ofFn_add,List.flatten_append]
  rfl

/-- Every randomized initial partition is a partition of the same literal
period string, with no fit conditioning or change of channel. -/
theorem motifPeriodWord_window {m : ℕ} (off : Fin m) (hi : 1 ≤ off.val ∧ off.val+1 < m)
    (t K z s : ℕ) (a : ℤ) (τ : ℝ) (hleft : (t:ℤ) ≤ a) (hright : a+(2^s:ℕ) ≤ t+K) :
    motifPeriodWord off hi (t+K+z) s a τ =
      pureAtomRun (initialPeriod m off.val) t ++ motifPeriodWord off hi K s (a-t) τ ++
      pureAtomRun (initialPeriod m off.val) z := by
  unfold motifPeriodWord
  rw [periodString_three]
  congr 2
  · rw [←periodString_constant off]
    congr 1
    funext i
    exact motifOffset_outside off hi s a τ i.val (Or.inl (by have H:=i.isLt; omega))
  · congr 1
    funext i
    rw [Nat.cast_add,motifOffset_translate]
  · rw [←periodString_constant off]
    congr 1
    funext i
    exact motifOffset_outside off hi s a τ (t+K+i.val) (Or.inr (by
      have H : (0:ℤ) ≤ i.val := by positivity
      omega))

theorem motifPeriodWord_length {m : ℕ} (off : Fin m) (hi : 1 ≤ off.val ∧ off.val+1 < m)
    (u s : ℕ) (X : ℤ) (τ : ℝ) :
    (motifPeriodWord off hi u s X τ).length=u*(2*m-1) := periodString_length _ _ _

end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open scoped Classical
namespace FiniteLaw
variable {α β : Type*} [Fintype α] [Fintype β]

theorem coordinateProduct_expect_pairs {n : ℕ} (P : Fin n → FiniteLaw α)
    (Q : Fin n → FiniteLaw β) (F : (Fin n → α×β) → ℝ) :
    (coordinateProduct (fun i => (P i).prod (Q i))).expect F=
      (coordinateProduct P).expect (fun a =>
        (coordinateProduct Q).expect (fun b => F (fun i => (a i,b i)))) := by
  induction n with
  | zero =>
    have H (a : Fin 0 → α×β) : a = fun i => Fin.elim0 i := by funext i; exact Fin.elim0 i
    have hF : F=fun _ => F (fun i => Fin.elim0 i) := by
      funext a
      exact congrArg F (H a)
    rw [hF]
    simp only [expect_const]
  | succ n ih =>
    rw [expect_coordinateProduct_succ,expect_prod,expect_coordinateProduct_succ]
    congr 1
    funext a
    simp_rw [ih,expect_coordinateProduct_succ Q]
    rw [expect_comm]
    congr 1
    funext x
    congr 1
    funext b
    congr 1
    funext y
    congr 1
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp

end FiniteLaw

/-- Three chronological streams, with side pairs independent across slots.
This forgets flags but does not separate any marks inside the central list. -/
def decodePairedEmission {Side α : Type*} {J : ℕ}
    (side : Side → List Bool) (central : α → List Bool) (z : Reports Side J × α) : List Bool :=
  coordinateWord (fun i => side (z.1 i).2.1) ++ central z.2 ++
    coordinateWord (fun i => side (z.1 i).2.2)

namespace PairedMechanisms
variable {Side α : Type*} [Fintype Side] [Fintype α] {J : ℕ}

theorem reportsGiven_paired_simulates (M : PairedMechanisms Side J) (b : Fin J → Bool)
    {q : ℝ} (side : Side → List Bool) (central : α → List Bool) (K : FiniteLaw α)
    (U V : Fin J → List Bool) (w : List Bool)
    (hfirst : ∀i,SimulatesTrace q (M.first i) side (U i))
    (hsecond : ∀i,SimulatesTrace q (M.second i) side (V i))
    (hK : SimulatesTrace q K central w) :
    SimulatesTrace q ((M.reportsGiven b).prod K) (decodePairedEmission side central)
      (coordinateWord (fun i => if b i then V i else U i) ++ w ++
        coordinateWord (fun i => if b i then U i else V i)) := by
  let P : Fin J → FiniteLaw Side := fun i => if b i then M.second i else M.first i
  let Q : Fin J → FiniteLaw Side := fun i => if b i then M.first i else M.second i
  have HP : ∀i,SimulatesTrace q (P i) side (if b i then V i else U i) := by
    intro i
    dsimp [P]
    cases h:b i
    · exact hfirst i
    · exact hsecond i
  have HQ : ∀i,SimulatesTrace q (Q i) side (if b i then U i else V i) := by
    intro i
    dsimp [Q]
    cases h:b i
    · exact hsecond i
    · exact hfirst i
  have H := ((coordinateProduct_simulates P side _ HP).append hK).append
    (coordinateProduct_simulates Q side _ HQ)
  intro F
  rw [←H F,FiniteLaw.expect_prod,FiniteLaw.expect_prod]
  change (M.reportsGiven b).expect (fun z => K.expect (fun x =>
    F (coordinateWord (fun i => side (z i).2.1) ++ central x ++
      coordinateWord (fun i => side (z i).2.2))))=_
  have hf := congrArg (fun L : FiniteLaw (Fin J → Side×Side) => L.expect (fun z =>
    K.expect (fun x => F (coordinateWord (fun i => side (z i).1) ++ central x ++
      coordinateWord (fun i => side (z i).2))))) (M.reportsGiven_forget b)
  rw [FiniteLaw.expect_map] at hf
  simp only [Function.comp_def] at hf
  rw [hf]
  have he : (fun i => FiniteLaw.orientedProd (M.first i) (M.second i) (b i))=
      fun i => (P i).prod (Q i) := by
    funext i
    cases h:b i <;> simp [FiniteLaw.orientedProd,P,Q,h]
  rw [he,FiniteLaw.coordinateProduct_expect_pairs]
  simp only [FiniteLaw.expect_prod]
  congr 1
  funext a
  rw [FiniteLaw.expect_comm]

end PairedMechanisms
end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open scoped Classical

/-- Exact initial paired prefix and complementary suffix sizes. -/
def initialPrefixPeriods {J : ℕ} (k : ℕ) (b : Fin J → Bool) : ℕ :=
  ∑ i : Fin J, (k+bitIndex (b i))
def initialSuffixPeriods {J : ℕ} (k : ℕ) (b : Fin J → Bool) : ℕ :=
  ∑ i : Fin J, (k+(1-bitIndex (b i)))

theorem initialPrefixPeriods_eval {J : ℕ} (k : ℕ) (b : Fin J → Bool) :
    initialPrefixPeriods k b=J*k+∑i,bitIndex (b i) := by
  simp [initialPrefixPeriods,Finset.sum_add_distrib]

theorem initialPairPeriods_total {J : ℕ} (k : ℕ) (b : Fin J → Bool) :
    initialPrefixPeriods k b+initialSuffixPeriods k b=J*(2*k+1) := by
  unfold initialPrefixPeriods initialSuffixPeriods
  rw [←Finset.sum_add_distrib]
  have H (i : Fin J) : (k+bitIndex (b i))+(k+(1-bitIndex (b i)))=2*k+1 := by
    cases h:b i <;> simp [bitIndex] <;> omega
  simp only [H,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id]

theorem initialPrefixPeriods_bounds {J : ℕ} (k : ℕ) (b : Fin J → Bool) :
    J*k ≤ initialPrefixPeriods k b ∧ initialPrefixPeriods k b ≤ J*k+J := by
  rw [initialPrefixPeriods_eval]
  have H : (∑i,bitIndex (b i)) ≤ J := by
    calc
      _ ≤ ∑_i : Fin J,1 := Finset.sum_le_sum (fun i _ => by cases b i <;> simp [bitIndex])
      _ = _ := by simp
  omega

theorem initial_paired_oracle_simulates {Side : Type*} [Fintype Side] {J K m : ℕ}
    (M : PairedMechanisms Side J) (k s : ℕ) (a : ℤ) (τ : ℝ)
    (off : Fin m) (hi : 1 ≤ off.val ∧ off.val+1 < m)
    (hsafe : SafeTaggedTuple (periodSlot (u:=K) (fun _ => off)))
    {q : ℝ} (hq : q∈Set.Ioo 0 1) (side : Side → List Bool)
    (hfirst : ∀i,SimulatesTrace q (M.first i) side (pureAtomRun (initialPeriod m off.val) k))
    (hsecond : ∀i,SimulatesTrace q (M.second i) side (pureAtomRun (initialPeriod m off.val) (k+1)))
    (ha : (J*k+J:ℕ) ≤ a) (ha' : a+(2^s:ℕ) ≤ (J*k+K:ℕ)) :
    SimulatesTrace q
      (M.emissionOracle (fun b => countedPrimitiveLaw (le_refl (K*m)) hq
        (defectTypes (signedPeriodDefects off hsafe s
          (a-(J*k:ℕ)-∑i,(bitIndex (b i):ℤ)) τ))))
      (decodePairedEmission side decodeBoundedMarks)
      (motifPeriodWord off hi (J*(2*k+1)+K) s a τ) := by
  rw [←M.emission_factorization]
  intro F
  rw [FiniteLaw.expect_mixture]
  have H (b : Fin J → Bool) :
      ((M.reportsGiven b).prod (countedPrimitiveLaw (le_refl (K*m)) hq
        (defectTypes (signedPeriodDefects off hsafe s
          (a-(J*k:ℕ)-∑i,(bitIndex (b i):ℤ)) τ)))).expect
        (fun z => F (decodePairedEmission side decodeBoundedMarks z))=
      listDeletionExpectation q (motifPeriodWord off hi (J*(2*k+1)+K) s a τ) F := by
    let t := initialPrefixPeriods k b
    let z := initialSuffixPeriods k b
    have ht := initialPrefixPeriods_bounds k b
    have htot : t+K+z=J*(2*k+1)+K := by
      have H:=initialPairPeriods_total k b
      dsimp [t,z]
      omega
    have hanchor : a-(J*k:ℕ)-∑i,(bitIndex (b i):ℤ)=a-t := by
      dsimp [t]
      rw [initialPrefixPeriods_eval]
      push_cast
      ring
    have hleft : (t:ℤ) ≤ a := by
      have H : (t:ℤ) ≤ (J*k+J:ℕ) := by exact_mod_cast ht.2
      omega
    have hright : a+(2^s:ℕ) ≤ (t:ℤ)+K := by
      have H : ((J*k:ℕ):ℤ) ≤ t := by exact_mod_cast ht.1
      simp only [Nat.cast_add] at ha'
      omega
    have hp : coordinateWord (fun i => if b i then
        pureAtomRun (initialPeriod m off.val) (k+1) else pureAtomRun (initialPeriod m off.val) k)=
        pureAtomRun (initialPeriod m off.val) t := by
      have h (i : Fin J) : (if b i then pureAtomRun (initialPeriod m off.val) (k+1) else
          pureAtomRun (initialPeriod m off.val) k)=pureAtomRun (initialPeriod m off.val) (k+bitIndex (b i)) := by
        cases b i <;> simp [bitIndex]
      simp_rw [h]
      exact coordinateWord_pureAtomRun _ _
    have hz : coordinateWord (fun i => if b i then
        pureAtomRun (initialPeriod m off.val) k else pureAtomRun (initialPeriod m off.val) (k+1))=
        pureAtomRun (initialPeriod m off.val) z := by
      have h (i : Fin J) : (if b i then pureAtomRun (initialPeriod m off.val) k else
          pureAtomRun (initialPeriod m off.val) (k+1))=pureAtomRun (initialPeriod m off.val) (k+(1-bitIndex (b i))) := by
        cases b i <;> simp [bitIndex]
      simp_rw [h]
      exact coordinateWord_pureAtomRun _ _
    have hc := countedPrimitiveLaw_simulates (le_refl (K*m)) hq
      (defectTypes (signedPeriodDefects off hsafe s (a-(J*k:ℕ)-∑i,(bitIndex (b i):ℤ)) τ))
    rw [signed_primitive_word off hi] at hc
    have hs := M.reportsGiven_paired_simulates b side decodeBoundedMarks _
      (fun _ => pureAtomRun (initialPeriod m off.val) k)
      (fun _ => pureAtomRun (initialPeriod m off.val) (k+1)) _ hfirst hsecond hc
    have hword : coordinateWord (fun i => if b i then
        pureAtomRun (initialPeriod m off.val) (k+1) else pureAtomRun (initialPeriod m off.val) k) ++
        motifPeriodWord off hi K s (a-(J*k:ℕ)-∑i,(bitIndex (b i):ℤ)) τ ++
        coordinateWord (fun i => if b i then pureAtomRun (initialPeriod m off.val) k else
          pureAtomRun (initialPeriod m off.val) (k+1))=
        motifPeriodWord off hi (J*(2*k+1)+K) s a τ := by
      rw [hp,hz,hanchor,←motifPeriodWord_window off hi t K z s a τ hleft hright,htot]
    rw [hword] at hs
    exact hs F
  simp only [H,FiniteLaw.expect_const]

end TraceReconstruction



noncomputable section
namespace TraceReconstruction
open scoped Classical

abbrev InitialMetadata (Side : Type*) (J N : ℕ) := Reports Side J × Fin (N+1)
abbrev InitialObservation (Side : Type*) (J N : ℕ) :=
  Σz : InitialMetadata Side J N, Fin z.2.val → PrimitiveMark

def initialMetadataLaw {Side : Type*} [Fintype Side] {J : ℕ}
    (M : PairedMechanisms Side J) (N : ℕ) {q : ℝ} (hq : q∈Set.Ioo 0 1) :
    FiniteLaw (InitialMetadata Side J N) :=
  M.reports.prod (boundedCountLaw (le_refl N) (1-primitiveErasure q) (primitiveRetention_mem hq))

def initialConditionalLaw {Side : Type*} [Fintype Side] {J K m : ℕ}
    (off : Fin m) (hsafe : SafeTaggedTuple (periodSlot (u:=K) (fun _ => off)))
    {q : ℝ} (hq : q∈Set.Ioo 0 1) (c : ℤ) (s : ℕ) (τ : ℝ)
    (z : InitialMetadata Side J (K*m)) : FiniteLaw (Fin z.2.val → PrimitiveMark) :=
  conditionalMotifLaw (by have H:=z.2.isLt; omega) off hsafe hq
    (posteriorAnchorSeries c (fun i => (z.1 i).1))
    (posteriorAnchorSeries_nonneg c _) (posteriorAnchorSeries_total c _) s τ

def initialSigmaLaw {Side : Type*} [Fintype Side] {J K m : ℕ}
    (M : PairedMechanisms Side J) (off : Fin m)
    (hsafe : SafeTaggedTuple (periodSlot (u:=K) (fun _ => off)))
    {q : ℝ} (hq : q∈Set.Ioo 0 1) (c : ℤ) (s : ℕ) (τ : ℝ) :
    FiniteLaw (InitialObservation Side J (K*m)) :=
  (initialMetadataLaw M (K*m) hq).sigma (initialConditionalLaw off hsafe hq c s τ)

def decodeInitialObservation {Side : Type*} {J N : ℕ} (side : Side → List Bool)
    (z : InitialObservation Side J N) : List Bool :=
  decodePairedEmission side decodeBoundedMarks (z.1.1,⟨z.1.2,z.2⟩)

theorem initialSigmaLaw_expect {Side : Type*} [Fintype Side] {J K m : ℕ}
    (M : PairedMechanisms Side J) (off : Fin m)
    (hsafe : SafeTaggedTuple (periodSlot (u:=K) (fun _ => off)))
    {q : ℝ} (hq : q∈Set.Ioo 0 1) (c : ℤ) (s : ℕ) (τ : ℝ)
    (F : Reports Side J × BoundedMarks (K*m) → ℝ) :
    (initialSigmaLaw M off hsafe hq c s τ).expect (fun z => F (z.1.1,⟨z.1.2,z.2⟩))=
    (M.emissionOracle (fun b => countedPrimitiveLaw (le_refl (K*m)) hq
      (defectTypes (signedPeriodDefects off hsafe s (c-∑i,(bitIndex (b i):ℤ)) τ)))).expect F := by
  unfold PairedMechanisms.emissionOracle
  rw [FiniteLaw.expect_joint]
  have H (z : Reports Side J) : (PairedMechanisms.orientationsGiven z).mixture
      (fun b => countedPrimitiveLaw (le_refl (K*m)) hq
        (defectTypes (signedPeriodDefects off hsafe s (c-∑i,(bitIndex (b i):ℤ)) τ)))=
      countedMotifLaw off hsafe hq (posteriorAnchorSeries c (fun i => (z i).1))
        (posteriorAnchorSeries_nonneg c _) (posteriorAnchorSeries_total c _) s τ :=
    countedMotifLaw_posterior off hsafe hq c (fun i => (z i).1) s τ
  simp_rw [H]
  simp only [initialSigmaLaw,initialMetadataLaw,FiniteLaw.expect_sigma,FiniteLaw.expect_prod,
    countedMotifLaw,initialConditionalLaw]

theorem initial_sigma_simulates {Side : Type*} [Fintype Side] {J K m : ℕ}
    (M : PairedMechanisms Side J) (k s : ℕ) (a : ℤ) (τ : ℝ)
    (off : Fin m) (hi : 1  ≤  off.val ∧ off.val+1  <  m)
    (hsafe : SafeTaggedTuple (periodSlot (u:=K) (fun _ => off)))
    {q : ℝ} (hq : q∈Set.Ioo 0 1) (side : Side → List Bool)
    (hfirst : ∀i,SimulatesTrace q (M.first i) side (pureAtomRun (initialPeriod m off.val) k))
    (hsecond : ∀i,SimulatesTrace q (M.second i) side (pureAtomRun (initialPeriod m off.val) (k+1)))
    (ha : (J*k+J:ℕ)  ≤  a) (ha' : a+(2^s:ℕ)  ≤  (J*k+K:ℕ)) :
    SimulatesTrace q (initialSigmaLaw M off hsafe hq (a-(J*k:ℕ)) s τ)
      (decodeInitialObservation side) (motifPeriodWord off hi (J*(2*k+1)+K) s a τ) := by
  intro F
  unfold decodeInitialObservation
  rw [initialSigmaLaw_expect M off hsafe hq (a-(J*k:ℕ)) s τ (fun z => F (decodePairedEmission side decodeBoundedMarks z))]
  exact initial_paired_oracle_simulates M k s a τ off hi hsafe hq side hfirst hsecond ha ha' F

/-- This is the literal count-typicality condition; it does not change the
 central count's original binomial law. -/
def initialCountAdmissible (N : ℕ) (q : ℝ) (l : Fin (N+1)) : Prop :=
  (l.val:ℝ)/(N:ℝ)∈Set.Icc (1-q^2) (1-q^2/4) ∧
    1  ≤  (N:ℝ)*((l.val:ℝ)/(N:ℝ))*(1-(l.val:ℝ)/(N:ℝ))

def initialMetadataGood {Side : Type*} {J N : ℕ} (q ω : ℝ)
    (z : InitialMetadata Side J N) : Prop :=
  initialCountAdmissible N q z.2 ∧ (J:ℝ)*ω^2/2  ≤  ∑i,(hiddenTrial (z.1 i).1:ℝ)

/-- The genuine initial metadata oracle is clipped by conditioning each
 admissible fiber only. Every bad report/count keeps its original mass and
 is replaced by a common law, so all discarded mass is charged. -/
theorem initial_sigma_clipped_exists {Side : Type*} [Fintype Side] {J K m R : ℕ}
    (M : PairedMechanisms Side J) (hK : 0 < K) (hm : 128 ≤ m) (hKm : K ≤ m)
    (hR : 0 < R) (off : Fin m) (hi : 1 ≤ off.val ∧ off.val+1 < m)
    (hoff : |(off.val:ℝ)-(m:ℝ)/2| ≤ 2)
    (hsafe : SafeTaggedTuple (periodSlot (u:=K) (fun _ => off)))
    (c : ℤ) (s k : ℕ) (hk : 1 ≤ k)
    (hleft : (K:ℝ)/3 ≤ 2*((c:ℝ)-J)+1)
    (hright : (K:ℝ)/3 ≤ 2*K-(2*((c:ℝ)+(2:ℝ)^s)+1))
    {q ω w V : ℝ} (hq : q∈Set.Ioc 0 (1/2:ℝ))
    (hM : ((2*(2^s):ℕ):ℝ) < (K:ℝ)/(3*(R+1:ℝ)))
    (hw : w=((6*(2*k:ℕ):ℝ)*(2/q)))
    (hscale : initialMomentRatio K m q w ≤ 1/2)
    (hclip : Real.sqrt (6*(4*(initialMomentRatio K m q w/(1-initialMomentRatio K m q w)))^k) ≤ 1/2)
    (hV : 0 ≤ V)
    (hbudget : ∀z : InitialMetadata Side J (K*m),initialMetadataGood q ω z →
      64*initialSignedBudget K m z.2.val R s (posteriorAnchorSeries c (fun i => (z.1 i).1))
        ((z.2.val:ℝ)/(K*m:ℕ)) q w ≤ V) :
    Nonempty (ClippedOracle
      (initialSigmaLaw M off hsafe ⟨hq.1,lt_of_le_of_lt hq.2 (by norm_num)⟩ c s (-1))
      (initialSigmaLaw M off hsafe ⟨hq.1,lt_of_le_of_lt hq.2 (by norm_num)⟩ c s 1) k
      (Real.sqrt (6*(4*(initialMomentRatio K m q w/(1-initialMomentRatio K m q w)))^k)+
        (initialMetadataLaw M (K*m) ⟨hq.1,lt_of_le_of_lt hq.2 (by norm_num)⟩).expect
          (fun z => if initialMetadataGood q ω z then 0 else 1)) V) := by
  apply ClippedOracle.assemble_good _ _ _ (initialMetadataGood q ω) k hk _ V (Real.sqrt_nonneg _) hV
  intro z hz
  have hmean : ((K*m:ℕ):ℝ)*((z.2.val:ℝ)/(K*m:ℕ))=z.2.val := by
    exact mul_div_cancel₀ _ (by exact_mod_cast (Nat.mul_ne_zero (by omega : K≠0) (by omega : m≠0)))
  have H := initial_conditional_clipped_exists hK hm hKm hR (by have H:=z.2.isLt; omega) off hi hoff hsafe
    (posteriorAnchorSeries c (fun i => (z.1 i).1)) (posteriorAnchorSeries_nonneg c _)
    (posteriorAnchorSeries_total c _) s k
    (posteriorAnchorSeries_central K s c _ (by simpa using hleft) hright) hk hq hz.1.1 hmean hz.1.2 hM hw hscale hclip
  exact ⟨(Classical.choice H).weaken le_rfl (hbudget z hz)⟩

end TraceReconstruction



noncomputable section
namespace TraceReconstruction
open scoped Classical

def purePeriodCoefficient {u m l : ℕ} (hl : l ≤ u*m) (off : Fin m) : (Fin l → Bool) → ℝ :=
  averagedCoefficient (uniformSubsetLaw l (by simpa using hl))
    (defectAtRank (Finset.univ.image (periodSlot (u:=u) (fun _ => off))))

theorem mixedMotifCoefficient_pure_rank_difference {u m l r : ℕ} (hl : l ≤ u*m) (off : Fin m)
    (hsafe : SafeTaggedTuple (periodSlot (u:=u) (fun _ => off)))
    (π : IntSeries) (hπsum : ∑X∈π.coeff.support,π.coeff X=1) (s : ℕ) (v : IncreasingTuple l r) :
    mixedMotifCoefficient hl off hsafe π s 1 (rankMask v)-purePeriodCoefficient hl off (rankMask v)=
      pureRankCoefficient hl off hsafe π s v := by
  unfold mixedMotifCoefficient purePeriodCoefficient pureRankCoefficient
  simp_rw [averaged_rank_coefficient hl _ v,mul_sub,Finset.sum_sub_distrib,←Finset.sum_mul,hπsum,one_mul]

/-- The pure comparison retains all low-degree cancellation, not just its
 total defect density. -/
def initialPureDegreeBound (u m r s : ℕ) (π : IntSeries) (θ : ℝ) (l : ℕ) : ℝ :=
  if r=0 then 0 else
    2*(Fintype.card (Fin r → GapDifference):ℝ)*
      (∑k : Fin r → GapDifference, if k=unchangedPattern r then 0 else purePatternBound u m r s π θ k)+
    2*((Fintype.card (IncreasingTuple u r):ℝ)*
      (2*(((r+1:ℕ):ℝ)*θ^r/binomialMass (u*m) θ l*(2*Real.exp (-(m:ℝ)/(1024*u))))))^2

theorem initialPureDegreeBound_nonneg (u m r s : ℕ) (π : IntSeries) (θ : ℝ) (l : ℕ) :
    0 ≤ initialPureDegreeBound u m r s π θ l := by
  unfold initialPureDegreeBound
  split_ifs
  · exact le_rfl
  · apply add_nonneg _ (by positivity)
    apply mul_nonneg (by positivity)
    apply Finset.sum_nonneg
    intro k _
    split_ifs
    · exact le_rfl
    · unfold purePatternBound
      split_ifs  <;> apply mul_nonneg _ (seriesL2Sq_nonneg _)
      all_goals dsimp only [periodDifferencePrefactor,lengthDifferenceConstant,periodCentralSumConstant]
      all_goals positivity

theorem pureMotif_degree_zero {u m l : ℕ} (hl : l ≤ u*m) (off : Fin m)
    (hsafe : SafeTaggedTuple (periodSlot (u:=u) (fun _ => off)))
    (π : IntSeries) (hπsum : ∑X∈π.coeff.support,π.coeff X=1) (s : ℕ) :
    (∑σ : Fin l → Bool,if monomialDegree σ=0 then
      (mixedMotifCoefficient hl off hsafe π s 1 σ-purePeriodCoefficient hl off σ)^2 else 0)=0 := by
  simp_rw [monomialDegree_eq_zero_iff]
  simp [mixedMotifCoefficient_empty hl off hsafe π hπsum,purePeriodCoefficient,averagedCoefficient_empty]

theorem pureMotif_degree_cancellation {u m l r : ℕ}
    (hu : 0 < u) (hm : 128 ≤ m) (hr : 0 < r) (hl : l ≤ u*m)
    (off : Fin m) (hoff : |(off.val:ℝ)-(m:ℝ)/2| ≤ 3)
    (hsafe : SafeTaggedTuple (periodSlot (u:=u) (fun _ => off)))
    (π : IntSeries) (hπ : ∀X,0 ≤ π.coeff X) (hπsum : ∑X∈π.coeff.support,π.coeff X=1)
    (s : ℕ) (hcentral : CentralMotifSupport u s π)
    {θ : ℝ} (hθ : θ∈Set.Ioo 0 1) (hhalf : 1/2 ≤ θ)
    (hmean : ((u*m:ℕ):ℝ)*θ=l) (hv : 1 ≤ ((u*m:ℕ):ℝ)*θ*(1-θ)) :
    (∑σ : Fin l → Bool,if monomialDegree σ=r then
      (mixedMotifCoefficient hl off hsafe π s 1 σ-purePeriodCoefficient hl off σ)^2 else 0) ≤ 
        initialPureDegreeBound u m r s π θ l := by
  refine (sum_degree_coeff_sq_le _).trans ?_
  simp_rw [mixedMotifCoefficient_pure_rank_difference hl off hsafe π hπsum s]
  simpa only [initialPureDegreeBound,ite_eq_right (by omega : r ≠ 0)] using
    initial_pure_energy hu hm hr hl off hoff hsafe π hπ hπsum s hcentral hθ hhalf hmean hv

theorem purePeriod_degree_geometric {u m l r : ℕ} (hl : l ≤ u*m) (hr : 0 < r)
    (hm : 32 ≤ m) (hum : u ≤ m) (off : Fin m) (hoff : |(off.val:ℝ)-(m:ℝ)/2| ≤ 3)
    {q θ : ℝ} (hq : q∈Set.Ioc 0 (1/2:ℝ))
    (hθ : θ∈Set.Icc (1-q^2) (1-q^2/4))
    (hmean : ((u*m:ℕ):ℝ)*θ=l) (hv : 1 ≤ ((u*m:ℕ):ℝ)*θ*(1-θ)) (w : ℝ) :
    w^(2*r)*(∑σ : Fin l → Bool,if monomialDegree σ=r then (purePeriodCoefficient hl off σ)^2 else 0) ≤ 
      (initialMomentRatio u m q w)^r := by
  have hw0 : 0 ≤ w^(2*r) := by rw [pow_mul]; positivity
  have hp : 0 ≤ 3*rankSchurConstant/q := by positivity [rankSchurConstant_pos,hq.1]
  by_cases hru : r ≤ u
  · have hb := period_degree_square_sum hl hr hru hm hum hq hθ hmean hv (fun _ => off)
      (fun _ => hoff) (fun _ _ => by simp)
    have hsqrt : Real.sqrt ((u:ℝ)/((m:ℝ)*r)) ≤ Real.sqrt ((u:ℝ)/m) := by
      apply Real.sqrt_le_sqrt
      apply div_le_div_of_nonneg_left (by positivity) (by exact_mod_cast (show 0 < m by omega))
      have hr1 : (1:ℝ) ≤ r := by exact_mod_cast hr
      nlinarith
    calc
      _  ≤  w^(2*r)*((3*rankSchurConstant/q)*Real.sqrt ((u:ℝ)/((m:ℝ)*r)))^r :=
        mul_le_mul_of_nonneg_left hb hw0
      _  ≤  w^(2*r)*((3*rankSchurConstant/q)*Real.sqrt ((u:ℝ)/m))^r := by gcongr
      _ = _ := by unfold initialMomentRatio; rw [pow_mul,mul_pow,mul_pow]; ring
  · have H := defect_degree_bound hl (periodSlot (u:=u) (fun _ => off)) (periodSlot_strictMono _) (by omega : u < r)
    change _=0 at H
    change w^(2*r)*_ ≤ _
    rw [show (∑σ : Fin l → Bool,if monomialDegree σ=r then (purePeriodCoefficient hl off σ)^2 else 0)=0 from H,mul_zero]
    exact pow_nonneg (by unfold initialMomentRatio; positivity [rankSchurConstant_pos,hq.1]) _

theorem pureMotif_degree_geometric {u m l r : ℕ} (hl : l ≤ u*m) (hr : 0 < r)
    (hm : 32 ≤ m) (hum : u ≤ m) (off : Fin m)
    (hi : 1 ≤ off.val ∧ off.val+1 < m) (hoff : |(off.val:ℝ)-(m:ℝ)/2| ≤ 2)
    (hsafe : SafeTaggedTuple (periodSlot (u:=u) (fun _ => off)))
    (π : IntSeries) (hπ : ∀X,0 ≤ π.coeff X) (hπsum : ∑X∈π.coeff.support,π.coeff X=1)
    (s : ℕ) {q θ : ℝ} (hq : q∈Set.Ioc 0 (1/2:ℝ))
    (hθ : θ∈Set.Icc (1-q^2) (1-q^2/4))
    (hmean : ((u*m:ℕ):ℝ)*θ=l) (hv : 1 ≤ ((u*m:ℕ):ℝ)*θ*(1-θ)) (w : ℝ) :
    w^(2*r)*(∑σ : Fin l → Bool,if monomialDegree σ=r then
      (mixedMotifCoefficient hl off hsafe π s 1 σ-purePeriodCoefficient hl off σ)^2 else 0) ≤ 
        4*(initialMomentRatio u m q w)^r := by
  have H := mul_le_mul_of_nonneg_left (degree_square_sub_le
    (mixedMotifCoefficient hl off hsafe π s 1) (purePeriodCoefficient hl off) r)
    (by rw [pow_mul]; positivity : 0 ≤ w^(2*r))
  have h1 := mixedMotif_degree_geometric hl hr hm hum off hi hoff hsafe π hπ hπsum s 1 hq hθ hmean hv w
  have h2 := purePeriod_degree_geometric hl hr hm hum off (hoff.trans (by norm_num)) hq hθ hmean hv w
  change _ ≤ initialMomentRatio u m q w ^r at h1
  nlinarith only [H,h1,h2]

def initialPureBudget (u m l R s : ℕ) (π : IntSeries) (θ q w : ℝ) : ℝ :=
  (∑r∈Finset.range R,w^(2*r)*initialPureDegreeBound u m r s π θ l)+
    4*(initialMomentRatio u m q w)^R/(1-initialMomentRatio u m q w)

theorem pure_initial_full_energy {u m l R : ℕ} (hu : 0 < u) (hm : 128 ≤ m)
    (hum : u ≤ m) (hR : 0 < R) (hl : l ≤ u*m) (off : Fin m)
    (hi : 1 ≤ off.val ∧ off.val+1 < m) (hoff : |(off.val:ℝ)-(m:ℝ)/2| ≤ 2)
    (hsafe : SafeTaggedTuple (periodSlot (u:=u) (fun _ => off)))
    (π : IntSeries) (hπ : ∀X,0 ≤ π.coeff X) (hπsum : ∑X∈π.coeff.support,π.coeff X=1)
    (s : ℕ) (hcentral : CentralMotifSupport u s π)
    {q θ w : ℝ} (hq : q∈Set.Ioc 0 (1/2:ℝ))
    (hθ : θ∈Set.Icc (1-q^2) (1-q^2/4))
    (hmean : ((u*m:ℕ):ℝ)*θ=l) (hv : 1 ≤ ((u*m:ℕ):ℝ)*θ*(1-θ))
    (hw : 0 ≤ w) (ha : initialMomentRatio u m q w < 1) :
    multilinearEnergy (fun σ => mixedMotifCoefficient hl off hsafe π s 1 σ-purePeriodCoefficient hl off σ) w ≤ 
      initialPureBudget u m l R s π θ q w := by
  have hq2 : q^2 ≤ (1/4:ℝ) := by
    calc q^2 ≤ (1/2:ℝ)^2 := pow_le_pow_left₀ hq.1.le hq.2 2
         _ = _ := by norm_num
  have hθ0 : θ∈Set.Ioo 0 1 := by constructor  <;> nlinarith [hq.1,hθ.1,hθ.2]
  have hhalf : 1/2 ≤ θ := by nlinarith [hθ.1]
  apply multilinearEnergy_low_high _ w _ 4 hw (by unfold initialMomentRatio; positivity [rankSchurConstant_pos,hq.1]) ha
    (by norm_num) (initialPureDegreeBound u m · s π θ l) _ _
    (fun r => initialPureDegreeBound_nonneg _ _ _ _ _ _ _)
  · intro r _hr
    by_cases hr0 : r=0
    · subst r
      rw [pureMotif_degree_zero hl off hsafe π hπsum s]
      exact initialPureDegreeBound_nonneg _ _ _ _ _ _ _
    · exact pureMotif_degree_cancellation hu hm (Nat.pos_of_ne_zero hr0) hl off (hoff.trans (by norm_num))
        hsafe π hπ hπsum s hcentral hθ0 hhalf hmean hv
  · intro r hr
    exact pureMotif_degree_geometric hl (by omega) (by omega) hum off hi hoff hsafe π hπ hπsum s hq hθ hmean hv w

end TraceReconstruction



noncomputable section
namespace TraceReconstruction
open scoped Classical

def purePeriodDensity {u m l : ℕ} (hl : l ≤ u*m) (off : Fin m) (q : ℝ) :
    (Fin l → PrimitiveMark) → ℝ := multilinear (purePeriodCoefficient hl off) (primitiveScore q)

theorem purePeriodDensity_nonneg {u m l : ℕ} (hl : l ≤ u*m) (off : Fin m)
    {q : ℝ} (hq : q∈Set.Ioo 0 1) (x : Fin l → PrimitiveMark) :
    0 ≤ purePeriodDensity hl off q x := by
  have H := (conditionalPrimitiveLaw hl q hq (defectTypes (periodSlot (u:=u) (fun _ => off)))).nonneg x
  rw [conditionalDefectLaw_density] at H
  exact nonneg_of_mul_nonneg_right H (primitive_product_mass_pos hq x)

theorem purePeriodDensity_total {u m l : ℕ} (hl : l ≤ u*m) (off : Fin m)
    {q : ℝ} (hq : q∈Set.Ioo 0 1) :
    ((primitiveMarkLaw q hq false).product l).expect (purePeriodDensity hl off q)=1 := by
  have H := (conditionalPrimitiveLaw hl q hq (defectTypes (periodSlot (u:=u) (fun _ => off)))).total
  simpa only [conditionalDefectLaw_density,FiniteLaw.expect,purePeriodDensity,purePeriodCoefficient] using H

theorem purePeriodLaw_withDensity {u m l : ℕ} (hl : l ≤ u*m) (off : Fin m)
    {q : ℝ} (hq : q∈Set.Ioo 0 1) :
    conditionalPrimitiveLaw hl q hq (defectTypes (periodSlot (u:=u) (fun _ => off)))=
      ((primitiveMarkLaw q hq false).product l).withDensity (purePeriodDensity hl off q)
        (purePeriodDensity_nonneg hl off hq) (purePeriodDensity_total hl off hq) := by
  apply FiniteLaw.ext
  funext x
  exact conditionalDefectLaw_density hl hq _ x

theorem purePeriod_centered_energy {u m l : ℕ} (hl : l ≤ u*m) (hm : 32 ≤ m) (hum : u ≤ m)
    (off : Fin m) (hoff : |(off.val:ℝ)-(m:ℝ)/2| ≤ 3)
    {q θ w : ℝ} (hq : q∈Set.Ioc 0 (1/2:ℝ))
    (hθ : θ∈Set.Icc (1-q^2) (1-q^2/4))
    (hmean : ((u*m:ℕ):ℝ)*θ=l) (hv : 1 ≤ ((u*m:ℕ):ℝ)*θ*(1-θ))
    (hw : 0 ≤ w) (ha : initialMomentRatio u m q w < 1) :
    multilinearEnergy (nonconstantCoefficient (purePeriodCoefficient hl off)) w ≤
      initialMomentRatio u m q w/(1-initialMomentRatio u m q w) := by
  have H := multilinearEnergy_low_high (R:=1)
    (nonconstantCoefficient (purePeriodCoefficient hl off)) w _ 1 hw
    (by unfold initialMomentRatio; positivity [rankSchurConstant_pos,hq.1]) ha (by norm_num) (fun _ => 0)
    (fun r hr => by
      have he : r=0 := by omega
      subst r
      rw [nonconstant_degree_zero])
    (fun r hr => by
      rw [nonconstant_degree_pos _ (by omega)]
      simpa only [one_mul] using purePeriod_degree_geometric hl (by omega) hm hum off hoff hq hθ hmean hv w)
    (fun _ => le_rfl)
  simpa using H

theorem purePeriod_centered_moment {u m l : ℕ} (hl : l ≤ u*m) (hm : 32 ≤ m) (hum : u ≤ m)
    (off : Fin m) (hoff : |(off.val:ℝ)-(m:ℝ)/2| ≤ 3) (k : ℕ) (hk : 1 ≤ k)
    {q θ w : ℝ} (hq : q∈Set.Ioc 0 (1/2:ℝ))
    (hθ : θ∈Set.Icc (1-q^2) (1-q^2/4))
    (hmean : ((u*m:ℕ):ℝ)*θ=l) (hv : 1 ≤ ((u*m:ℕ):ℝ)*θ*(1-θ))
    (hw : w=((6*(2*k:ℕ):ℝ)*(2/q))) (ha : initialMomentRatio u m q w < 1) :
    ((primitiveMarkLaw q ⟨hq.1,lt_of_le_of_lt hq.2 (by norm_num)⟩ false).product l).evenMomentSq
      (fun x => purePeriodDensity hl off q x-1) k ≤
      initialMomentRatio u m q w/(1-initialMomentRatio u m q w) := by
  have hq' : q∈Set.Ioo 0 1 := ⟨hq.1,lt_of_le_of_lt hq.2 (by norm_num)⟩
  have he : (fun x => purePeriodDensity hl off q x-1)=
      multilinear (nonconstantCoefficient (purePeriodCoefficient hl off)) (primitiveScore q) := by
    funext x
    rw [nonconstant_multilinear]
    simp only [purePeriodCoefficient,averagedCoefficient_empty,purePeriodDensity]
  rw [he]
  apply (multilinear_moment_sq_scaled (primitiveMarkLaw q hq' false) (primitiveScore q) k hk
    (primitive_score_centered hq') (div_pos (by norm_num) hq.1) (primitive_score_evenMoment hq' k) l _).trans
  rw [←hw]
  exact purePeriod_centered_energy hl hm hum off hoff hq hθ hmean hv (by rw [hw]; positivity [hq.1]) ha

theorem initial_pure_moment {u m l R : ℕ} (hu : 0 < u) (hm : 128 ≤ m)
    (hum : u ≤ m) (hR : 0 < R) (hl : l ≤ u*m) (off : Fin m)
    (hi : 1 ≤ off.val ∧ off.val+1 < m) (hoff : |(off.val:ℝ)-(m:ℝ)/2| ≤ 2)
    (hsafe : SafeTaggedTuple (periodSlot (u:=u) (fun _ => off)))
    (π : IntSeries) (hπ : ∀X,0 ≤ π.coeff X) (hπsum : ∑X∈π.coeff.support,π.coeff X=1)
    (s k : ℕ) (hcentral : CentralMotifSupport u s π) (hk : 1 ≤ k)
    {q θ w : ℝ} (hq : q∈Set.Ioc 0 (1/2:ℝ))
    (hθ : θ∈Set.Icc (1-q^2) (1-q^2/4))
    (hmean : ((u*m:ℕ):ℝ)*θ=l) (hv : 1 ≤ ((u*m:ℕ):ℝ)*θ*(1-θ))
    (hw : w=((6*(2*k:ℕ):ℝ)*(2/q))) (ha : initialMomentRatio u m q w < 1) :
    ((primitiveMarkLaw q ⟨hq.1,lt_of_le_of_lt hq.2 (by norm_num)⟩ false).product l).evenMomentSq
      (fun x => initialMotifDensity hl off hsafe π s 1 q x-purePeriodDensity hl off q x) k ≤
        initialPureBudget u m l R s π θ q w := by
  have hq' : q∈Set.Ioo 0 1 := ⟨hq.1,lt_of_le_of_lt hq.2 (by norm_num)⟩
  have he : (fun x => initialMotifDensity hl off hsafe π s 1 q x-purePeriodDensity hl off q x)=
      multilinear (fun σ => mixedMotifCoefficient hl off hsafe π s 1 σ-purePeriodCoefficient hl off σ)
        (primitiveScore q) := by funext x; exact (multilinear_sub _ _ _ _).symm
  rw [he]
  apply (multilinear_moment_sq_scaled (primitiveMarkLaw q hq' false) (primitiveScore q) k hk
    (primitive_score_centered hq') (div_pos (by norm_num) hq.1) (primitive_score_evenMoment hq' k) l _).trans
  rw [←hw]
  exact pure_initial_full_energy hu hm hum hR hl off hi hoff hsafe π hπ hπsum s hcentral hq hθ hmean hv
    (by rw [hw]; positivity [hq.1]) ha

theorem initial_pure_conditional_clipped_exists {u m l R : ℕ} (hu : 0 < u) (hm : 128 ≤ m)
    (hum : u ≤ m) (hR : 0 < R) (hl : l ≤ u*m) (off : Fin m)
    (hi : 1 ≤ off.val ∧ off.val+1 < m) (hoff : |(off.val:ℝ)-(m:ℝ)/2| ≤ 2)
    (hsafe : SafeTaggedTuple (periodSlot (u:=u) (fun _ => off)))
    (π : IntSeries) (hπ : ∀X,0 ≤ π.coeff X) (hπsum : ∑X∈π.coeff.support,π.coeff X=1)
    (s k : ℕ) (hcentral : CentralMotifSupport u s π) (hk : 1 ≤ k)
    {q θ w : ℝ} (hq : q∈Set.Ioc 0 (1/2:ℝ))
    (hθ : θ∈Set.Icc (1-q^2) (1-q^2/4))
    (hmean : ((u*m:ℕ):ℝ)*θ=l) (hv : 1 ≤ ((u*m:ℕ):ℝ)*θ*(1-θ))
    (hw : w=((6*(2*k:ℕ):ℝ)*(2/q))) (hscale : initialMomentRatio u m q w ≤ 1/2)
    (hclip : Real.sqrt (6*(4*(initialMomentRatio u m q w/(1-initialMomentRatio u m q w)))^k) ≤ 1/2) :
    Nonempty (ClippedOracle
      (conditionalPrimitiveLaw hl q ⟨hq.1,lt_of_le_of_lt hq.2 (by norm_num)⟩
        (defectTypes (periodSlot (u:=u) (fun _ => off))))
      (conditionalMotifLaw hl off hsafe ⟨hq.1,lt_of_le_of_lt hq.2 (by norm_num)⟩ π hπ hπsum s 1) k
      (Real.sqrt (6*(4*(initialMomentRatio u m q w/(1-initialMomentRatio u m q w)))^k))
      (64*initialPureBudget u m l R s π θ q w)) := by
  have hq' : q∈Set.Ioo 0 1 := ⟨hq.1,lt_of_le_of_lt hq.2 (by norm_num)⟩
  let A := (primitiveMarkLaw q hq' false).product l
  let f := purePeriodDensity hl off q
  let g := initialMotifDensity hl off hsafe π s 1 q
  let U := initialMomentRatio u m q w/(1-initialMomentRatio u m q w)
  have ha : initialMomentRatio u m q w < 1 := by linarith
  have hz : 0 ≤ initialMomentRatio u m q w := by unfold initialMomentRatio; positivity [rankSchurConstant_pos,hq.1]
  have hU : 0 ≤ U := div_nonneg hz (sub_nonneg.mpr ha.le)
  have hU1 : U ≤ 1 := (div_le_iff₀ (sub_pos.mpr ha)).mpr (by linarith)
  have hf : A.expect (fun x => |f x-1|^(2*k)) ≤ U^k :=
    A.expect_even_pow_le_of_moment _ k hk (purePeriod_centered_moment hl (by omega) hum off
      (hoff.trans (by norm_num)) k hk hq hθ hmean hv hw ha)
  have hg : A.expect (fun x => |g x-1|^(2*k)) ≤ U^k :=
    A.expect_even_pow_le_of_moment _ k hk (initial_centered_moment hl (by omega) hum off hi hoff hsafe π hπ hπsum s k hk 1 hq hθ hmean hv hw ha)
  have hsig := initial_pure_moment hu hm hum hR hl off hi hoff hsafe π hπ hπsum s k hcentral hk hq hθ hmean hv hw ha
  have hV := (A.evenMomentSq_nonneg (fun x => g x-f x) k).trans hsig
  have hsig' := A.expect_even_pow_le_of_moment _ k hk hsig
  rw [purePeriodLaw_withDensity hl off hq',initialMotifLaw_withDensity hl off hsafe π hπ hπsum s 1 hq']
  have H := A.exists_clippedOracle f g
    (purePeriodDensity_nonneg hl off hq') (initialMotifDensity_nonneg hl off hsafe π hπ hπsum s 1 hq')
    (purePeriodDensity_total hl off hq') (initialMotifDensity_mean hl off hsafe π hπ hπsum s 1 hq')
    Finset.univ 0 (by simp [FiniteLaw.eventMass]) (by simp [FiniteLaw.eventMass]) k hk U hU hU1 hf hg
    (initialPureBudget u m l R s π θ q w) hV (by simpa only [Finset.mem_univ,ite_true] using hsig')
    (by simpa only [zero_add] using hclip)
  simpa only [zero_add] using H

end TraceReconstruction



noncomputable section
namespace TraceReconstruction
open scoped Classical

/-- A common finite decoder transfers normalized clipping to actual complete
 traces. Neither interface is permitted to assume the main lower bound. -/
theorem ClippedOracle.tracePair {α : Type} [Fintype α] {P Q : FiniteLaw α}
    {q e V : ℝ} {x y : List Bool} {k : ℕ} (f : α → List Bool)
    (C : ClippedOracle P Q k e V) (hP : SimulatesTrace q P f x)
    (hQ : SimulatesTrace q Q f y) : Nonempty (OracleTracePair q x y k e V) := by
  refine ⟨{
    Outcome := α
    finiteOutcome := inferInstance
    first := C.first
    second := C.second
    decode := f
    score := C.score
    density := C.density
    likelihood_nonneg := C.likelihood_nonneg
    centered := C.centered
    moment := C.moment
    first_simulation := ?_
    second_simulation := ?_
  }⟩
  · simpa using hP.approximate.of_tv C.first_tv
  · simpa using hQ.approximate.of_tv C.second_tv

def initialPureConditionalLaw {Side : Type*} {J K m : ℕ} (off : Fin m)
    {q : ℝ} (hq : q∈Set.Ioo 0 1) (z : InitialMetadata Side J (K*m)) :
    FiniteLaw (Fin z.2.val → PrimitiveMark) :=
  conditionalPrimitiveLaw (by have H:=z.2.isLt; omega) q hq
    (defectTypes (periodSlot (u:=K) (fun _ => off)))

def initialPureSigmaLaw {Side : Type*} [Fintype Side] {J K m : ℕ}
    (M : PairedMechanisms Side J) (off : Fin m) {q : ℝ} (hq : q∈Set.Ioo 0 1) :
    FiniteLaw (InitialObservation Side J (K*m)) :=
  (initialMetadataLaw M (K*m) hq).sigma (initialPureConditionalLaw off hq)

theorem initialPureSigmaLaw_expect {Side : Type*} [Fintype Side] {J K m : ℕ}
    (M : PairedMechanisms Side J) (off : Fin m) {q : ℝ} (hq : q∈Set.Ioo 0 1)
    (F : Reports Side J × BoundedMarks (K*m) → ℝ) :
    (initialPureSigmaLaw M off hq).expect (fun z => F (z.1.1,⟨z.1.2,z.2⟩))=
    (M.emissionOracle (fun _ => countedPrimitiveLaw (le_refl (K*m)) hq
      (defectTypes (periodSlot (u:=K) (fun _ => off))))).expect F := by
  simp only [initialPureSigmaLaw,initialMetadataLaw,FiniteLaw.expect_sigma,
    FiniteLaw.expect_prod,PairedMechanisms.emissionOracle,FiniteLaw.expect_joint,
    FiniteLaw.expect_mixture,FiniteLaw.expect_const,initialPureConditionalLaw,
    countedPrimitiveLaw,FiniteLaw.expect_sigma]
  have hl (l : Fin (K*m+1)) : l.val ≤ K*m := Nat.le_of_lt_succ l.isLt
  simp only [boundedConditionalPrimitiveLaw,hl,dite_eq_left]

theorem initial_pure_sigma_simulates {Side : Type*} [Fintype Side] {J K m : ℕ}
    (M : PairedMechanisms Side J) (k : ℕ) (off : Fin m)
    {q : ℝ} (hq : q∈Set.Ioo 0 1) (side : Side → List Bool)
    (hfirst : ∀i,SimulatesTrace q (M.first i) side (pureAtomRun (initialPeriod m off.val) k))
    (hsecond : ∀i,SimulatesTrace q (M.second i) side (pureAtomRun (initialPeriod m off.val) (k+1))) :
    SimulatesTrace q (initialPureSigmaLaw (K:=K) M off hq) (decodeInitialObservation side)
      (pureAtomRun (initialPeriod m off.val) (J*(2*k+1)+K)) := by
  intro F
  unfold decodeInitialObservation
  rw [initialPureSigmaLaw_expect M off hq (fun z => F (decodePairedEmission side decodeBoundedMarks z)),
    ←M.emission_factorization,FiniteLaw.expect_mixture]
  have H (b : Fin J → Bool) :
      ((M.reportsGiven b).prod (countedPrimitiveLaw (le_refl (K*m)) hq
        (defectTypes (periodSlot (u:=K) (fun _ => off))))).expect
        (fun z => F (decodePairedEmission side decodeBoundedMarks z))=
      listDeletionExpectation q (pureAtomRun (initialPeriod m off.val) (J*(2*k+1)+K)) F := by
    have hc := countedPrimitiveLaw_simulates (le_refl (K*m)) hq (defectTypes (periodSlot (u:=K) (fun _ => off)))
    rw [periodic_primitive_word,periodString_constant] at hc
    have hs := M.reportsGiven_paired_simulates b side decodeBoundedMarks _
      (fun _ => pureAtomRun (initialPeriod m off.val) k)
      (fun _ => pureAtomRun (initialPeriod m off.val) (k+1)) _ hfirst hsecond hc
    have hp : coordinateWord (fun i => if b i then pureAtomRun (initialPeriod m off.val) (k+1)
        else pureAtomRun (initialPeriod m off.val) k)=
        pureAtomRun (initialPeriod m off.val) (initialPrefixPeriods k b) := by
      have h (i : Fin J) : (if b i then pureAtomRun (initialPeriod m off.val) (k+1) else
          pureAtomRun (initialPeriod m off.val) k)=pureAtomRun (initialPeriod m off.val) (k+bitIndex (b i)) := by
        cases b i <;> simp [bitIndex]
      simp_rw [h]
      exact coordinateWord_pureAtomRun _ _
    have hz : coordinateWord (fun i => if b i then pureAtomRun (initialPeriod m off.val) k
        else pureAtomRun (initialPeriod m off.val) (k+1))=
        pureAtomRun (initialPeriod m off.val) (initialSuffixPeriods k b) := by
      have h (i : Fin J) : (if b i then pureAtomRun (initialPeriod m off.val) k else
          pureAtomRun (initialPeriod m off.val) (k+1))=pureAtomRun (initialPeriod m off.val) (k+(1-bitIndex (b i))) := by
        cases b i <;> simp [bitIndex]
      simp_rw [h]
      exact coordinateWord_pureAtomRun _ _
    rw [hp,hz,←pureAtomRun_add,←pureAtomRun_add] at hs
    have ht : initialPrefixPeriods k b+K+initialSuffixPeriods k b=J*(2*k+1)+K := by
      have ht:=initialPairPeriods_total k b
      omega
    rw [ht] at hs
    exact hs F
  simp only [H,FiniteLaw.expect_const]

theorem initial_pure_sigma_clipped_exists {Side : Type*} [Fintype Side] {J K m R : ℕ}
    (M : PairedMechanisms Side J) (hK : 0 < K) (hm : 128 ≤ m) (hKm : K ≤ m)
    (hR : 0 < R) (off : Fin m) (hi : 1 ≤ off.val ∧ off.val+1 < m)
    (hoff : |(off.val:ℝ)-(m:ℝ)/2| ≤ 2)
    (hsafe : SafeTaggedTuple (periodSlot (u:=K) (fun _ => off)))
    (c : ℤ) (s k : ℕ) (hk : 1 ≤ k)
    (hleft : (K:ℝ)/3 ≤ 2*((c:ℝ)-J)+1)
    (hright : (K:ℝ)/3 ≤ 2*K-(2*((c:ℝ)+(2:ℝ)^s)+1))
    {q ω w V : ℝ} (hq : q∈Set.Ioc 0 (1/2:ℝ))
    (hw : w=((6*(2*k:ℕ):ℝ)*(2/q)))
    (hscale : initialMomentRatio K m q w ≤ 1/2)
    (hclip : Real.sqrt (6*(4*(initialMomentRatio K m q w/(1-initialMomentRatio K m q w)))^k) ≤ 1/2)
    (hV : 0 ≤ V)
    (hbudget : ∀z : InitialMetadata Side J (K*m),initialMetadataGood q ω z →
      64*initialPureBudget K m z.2.val R s (posteriorAnchorSeries c (fun i => (z.1 i).1))
        ((z.2.val:ℝ)/(K*m:ℕ)) q w ≤ V) :
    Nonempty (ClippedOracle
      (initialPureSigmaLaw M off ⟨hq.1,lt_of_le_of_lt hq.2 (by norm_num)⟩)
      (initialSigmaLaw M off hsafe ⟨hq.1,lt_of_le_of_lt hq.2 (by norm_num)⟩ c s 1) k
      (Real.sqrt (6*(4*(initialMomentRatio K m q w/(1-initialMomentRatio K m q w)))^k)+
        (initialMetadataLaw M (K*m) ⟨hq.1,lt_of_le_of_lt hq.2 (by norm_num)⟩).expect
          (fun z => if initialMetadataGood q ω z then 0 else 1)) V) := by
  apply ClippedOracle.assemble_good _ _ _ (initialMetadataGood q ω) k hk _ V (Real.sqrt_nonneg _) hV
  intro z hz
  have hmean : ((K*m:ℕ):ℝ)*((z.2.val:ℝ)/(K*m:ℕ))=z.2.val := by
    exact mul_div_cancel₀ _ (by exact_mod_cast (Nat.mul_ne_zero (by omega : K≠0) (by omega : m≠0)))
  have H := initial_pure_conditional_clipped_exists hK hm hKm hR (by have H:=z.2.isLt; omega) off hi hoff hsafe
    (posteriorAnchorSeries c (fun i => (z.1 i).1)) (posteriorAnchorSeries_nonneg c _)
    (posteriorAnchorSeries_total c _) s k
    (posteriorAnchorSeries_central K s c _ (by simpa using hleft) hright) hk hq hz.1.1 hmean hz.1.2 hw hscale hclip
  exact ⟨(Classical.choice H).weaken le_rfl (hbudget z hz)⟩

end TraceReconstruction



noncomputable section
namespace TraceReconstruction
open scoped Classical

/-- The half-mean hidden-count event yields the correct L², not supremum,
 exponent J^{-s-1/2} in the initial Prouhet cancellation. -/
def hiddenSignedL2Bound (J s : ℕ) (ω : ℝ) : ℝ :=
  ((2:ℝ)^(s*s))^2*((2*Real.sqrt (4*((s:ℝ)+1)/((J:ℝ)*ω^2+2)))^s)^2*
    Real.sqrt (4*((s:ℝ)+1)/((J:ℝ)*ω^2+2))

def hiddenUnsignedL2Bound (J s : ℕ) (ω : ℝ) : ℝ :=
  ((2:ℝ)^s)^2*hiddenBinomialCap J ω

theorem hiddenSignedL2Bound_nonneg (J s : ℕ) (ω : ℝ) : 0≤hiddenSignedL2Bound J s ω := by
  unfold hiddenSignedL2Bound; positivity

theorem hiddenUnsignedL2Bound_nonneg (J s : ℕ) (ω : ℝ) : 0≤hiddenUnsignedL2Bound J s ω := by
  exact mul_nonneg (sq_nonneg _) (hiddenBinomialCap_nonneg _ _)

theorem hidden_quotient_bound (J G s : ℕ) (ω : ℝ) (h : (J:ℝ)*ω^2/2≤G) :
    binomialBound (G/(s+1))≤Real.sqrt (4*((s:ℝ)+1)/((J:ℝ)*ω^2+2)) := by
  apply (binomialBound_quotient_le G s).trans
  apply Real.sqrt_le_sqrt
  apply (div_le_div_iff₀ (by positivity : (0:ℝ)<(G:ℝ)+1)
    (by positivity : (0:ℝ)<(J:ℝ)*ω^2+2)).mpr
  have hh := mul_le_mul_of_nonneg_left h (by positivity : (0:ℝ)≤4*((s:ℝ)+1))
  nlinarith

theorem posteriorAnchorSeries_signed_L2 {J : ℕ} (d : Fin J→Option Bool) (c : ℤ) (s : ℕ) (ω : ℝ)
    (h : (J:ℝ)*ω^2/2≤∑i,(hiddenTrial (d i):ℝ)) :
    seriesL2Sq (prouhetSeries s*posteriorAnchorSeries c d)≤hiddenSignedL2Bound J s ω := by
  have hn : (J:ℝ)*ω^2/2≤((∑i,hiddenTrial (d i):ℕ):ℝ) := by simpa only [Nat.cast_sum] using h
  have hb := hidden_quotient_bound J (∑i,hiddenTrial (d i)) s ω hn
  apply (translated_binomial_smoothing (∑i,hiddenTrial (d i)) s _).trans
  unfold hiddenSignedL2Bound
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply mul_le_mul
  · apply pow_le_pow_left₀ (by unfold binomialBound; positivity)
    exact pow_le_pow_left₀ (by unfold binomialBound; positivity) (mul_le_mul_of_nonneg_left hb (by norm_num)) _
  · exact hb
  · exact Real.sqrt_nonneg _
  · positivity

theorem posteriorAnchorSeries_unsigned_L2 {J : ℕ} (d : Fin J→Option Bool) (c : ℤ) (s : ℕ) (ω : ℝ)
    (h : (J:ℝ)*ω^2/2≤∑i,(hiddenTrial (d i):ℝ)) :
    seriesL2Sq (geomSeries (2^s)*posteriorAnchorSeries c d)≤hiddenUnsignedL2Bound J s ω := by
  have hn : (J:ℝ)*ω^2/2≤((∑i,hiddenTrial (d i):ℕ):ℝ) := by simpa only [Nat.cast_sum] using h
  calc
    _ ≤ seriesL1 (geomSeries (2^s))^2*seriesL2Sq (posteriorAnchorSeries c d) := seriesL2Sq_mul_le _ _
    _ ≤ ((2:ℝ)^s)^2*hiddenBinomialCap J ω := by
      apply mul_le_mul
      · exact pow_le_pow_left₀ (seriesL1_nonneg _) (by exact_mod_cast geomSeries_L1_le (2^s)) _
      · rw [posteriorAnchorSeries,translateSeries_L2Sq]
        exact (fairSeries_L2Sq_bound _).trans (hidden_binomial_bound J _ ω hn)
      · exact seriesL2Sq_nonneg _
      · positivity

end TraceReconstruction



noncomputable section
namespace TraceReconstruction
open scoped Classical

def initialDifferenceCap (d : ℕ) (q : ℝ) : ℝ :=
  2*Real.sqrt (8*((d:ℝ)+1)/q^2)

theorem initial_theta_variance {q θ : ℝ} (hq : q∈Set.Ioc 0 (1/2:ℝ))
    (hθ : θ∈Set.Icc (1-q^2) (1-q^2/4)) :
    θ∈Set.Ioo 0 1 ∧ 1/2≤θ ∧ q^2/8≤θ*(1-θ) := by
  have hq2 : q^2≤1/4 := by nlinarith [hq.1,hq.2]
  have hs : 0<q^2 := sq_pos_of_pos hq.1
  have hh : 1/2≤θ := by linarith [hθ.1]
  refine ⟨⟨by linarith,by linarith [hθ.2]⟩,hh,?_⟩
  have H := mul_le_mul hh (show q^2/4≤1-θ by linarith [hθ.2])
    (by positivity : (0:ℝ)≤q^2/4) (by linarith : 0≤θ)
  nlinarith

theorem initialDifferenceCap_bound (d : ℕ) {q θ : ℝ}
    (hq : q∈Set.Ioc 0 (1/2:ℝ)) (hθ : θ∈Set.Icc (1-q^2) (1-q^2/4)) :
    lengthDifferenceConstant d θ≤ initialDifferenceCap d q := by
  have ht := initial_theta_variance hq hθ
  unfold lengthDifferenceConstant initialDifferenceCap
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.sqrt_le_sqrt
  apply (div_le_div_iff₀ (mul_pos ht.1.1 (sub_pos.mpr ht.1.2)) (sq_pos_of_pos hq.1)).mpr
  have H := mul_le_mul_of_nonneg_left ht.2.2 (by positivity : (0:ℝ)≤8*((d:ℝ)+1))
  nlinarith

/-- All q dependence of a fixed rank-difference estimate is exposed here.
 The powers of u and m are retained exactly, including both large-gap gains. -/
def initialPrefactorCap (u m r d : ℕ) (q : ℝ) : ℝ :=
  144*((u*m:ℕ):ℝ)*(2:ℝ)^(2*r)*(initialDifferenceCap d q)^(2*d+r+2) /
    (((m:ℝ)/4)^d*Real.sqrt ((u:ℝ)*m/(2*(r+1:ℝ)))*
      (Real.sqrt ((m:ℝ)/4))^(r+1))

theorem initialPrefactorCap_nonneg (u m r d : ℕ) (q : ℝ) : 0≤ initialPrefactorCap u m r d q := by
  unfold initialPrefactorCap initialDifferenceCap
  positivity

theorem initial_prefactor_bound (u m r d : ℕ) {q θ : ℝ}
    (hq : q∈Set.Ioc 0 (1/2:ℝ)) (hθ : θ∈Set.Icc (1-q^2) (1-q^2/4)) :
    periodDifferencePrefactor u m r d θ≤ initialPrefactorCap u m r d q := by
  unfold periodDifferencePrefactor initialPrefactorCap
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact pow_le_pow_left₀ (by unfold lengthDifferenceConstant; positivity) (initialDifferenceCap_bound d hq hθ) _

theorem binomial_mean_inverse_le_sqrt {n l : ℕ} {θ : ℝ}
    (hθ : θ∈Set.Ioo 0 1) (hl : l≤n) (hmean : (n:ℝ)*θ=l)
    (hv : 1≤(n:ℝ)*θ*(1-θ)) :
    (binomialMass n θ l)⁻¹≤12*Real.sqrt (n:ℝ) := by
  have h0 : 0≤(binomialMass n θ l)⁻¹ := inv_nonneg.mpr (binomialMass_nonneg n l ⟨hθ.1.le,hθ.2.le⟩)
  have hi := binomialMass_mean_inverse_sq n l hθ hl hmean hv
  have hv' : (n:ℝ)*θ*(1-θ)≤n := by
    have h := mul_le_mul_of_nonneg_left (show θ*(1-θ)≤1 by nlinarith [sq_nonneg θ]) (Nat.cast_nonneg (α:=ℝ) n)
    nlinarith
  have hs := Real.sq_sqrt (Nat.cast_nonneg (α:=ℝ) n)
  nlinarith [Real.sqrt_nonneg (n:ℝ)]

def initialRankTailCap (u m r : ℕ) : ℝ :=
  2*((Fintype.card (IncreasingTuple u r):ℝ)*
    (48*((r+1:ℕ):ℝ)*Real.sqrt (u*m:ℕ)*Real.exp (-(m:ℝ)/(1024*u))))^2

theorem initial_rank_tail_bound {u m l : ℕ} (r : ℕ) {θ : ℝ}
    (hθ : θ∈Set.Ioo 0 1) (hl : l≤u*m) (hmean : ((u*m:ℕ):ℝ)*θ=l)
    (hv : 1≤((u*m:ℕ):ℝ)*θ*(1-θ)) :
    2*((Fintype.card (IncreasingTuple u r):ℝ)*
      (2*(((r+1:ℕ):ℝ)*θ^r/binomialMass (u*m) θ l*(2*Real.exp (-(m:ℝ)/(1024*u))))))^2 ≤
    initialRankTailCap u m r := by
  have hp : θ^r≤1 := pow_le_one₀ hθ.1.le hθ.2.le
  have hi := binomial_mean_inverse_le_sqrt hθ hl hmean hv
  have hn : 0≤(binomialMass (u*m) θ l)⁻¹ := inv_nonneg.mpr (binomialMass_nonneg _ _ ⟨hθ.1.le,hθ.2.le⟩)
  unfold initialRankTailCap
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  have hb := binomialMass_nonneg (u*m) l ⟨hθ.1.le,hθ.2.le⟩
  apply pow_le_pow_left₀ (by
    exact mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (by norm_num)
      (mul_nonneg (div_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hθ.1.le _)) hb)
        (by positivity))))
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have H := mul_le_mul hp hi hn (by norm_num : (0:ℝ)≤1)
  have HH := mul_le_mul_of_nonneg_left H (by positivity : (0:ℝ)≤4*((r+1:ℕ):ℝ)*Real.exp (-(m:ℝ)/(1024*u)))
  simp only [div_eq_mul_inv,one_mul] at *
  nlinarith only [HH]

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical

/-- The central binomial typical interval also guarantees the rank-kernel
 variance condition, rather than imposing it by conditioning. -/
theorem initialCountAdmissible_of_near {N : ℕ} {q : ℝ}
    (hq : q∈Set.Ioc 0 (1/2:ℝ)) (hscale : 8≤(N:ℝ)*q^2) (l : Fin (N+1))
    (hnear : |(l.val:ℝ)-(N:ℝ)*(1-q^2/2)|<(N:ℝ)*q^2/4) :
    initialCountAdmissible N q l := by
  have hN : (0:ℝ)<N := by
    have h0 : (0:ℝ)≤N := Nat.cast_nonneg N
    by_contra H
    have hn : (N:ℝ)=0 := le_antisymm (le_of_not_gt H) h0
    rw [hn,zero_mul] at hscale
    norm_num at hscale
  have hq2 : q^2≤1/4 := by nlinarith [hq.1,hq.2]
  let θ : ℝ := (l.val:ℝ)/(N:ℝ)
  have he : (N:ℝ)*θ=l.val := mul_div_cancel₀ _ hN.ne'
  have hθ : θ∈Set.Icc (1-q^2) (1-q^2/4) := by
    have hn := abs_lt.mp hnear
    constructor
    · apply le_of_lt
      apply (mul_lt_mul_iff_right₀ hN).mp
      nlinarith [sq_nonneg q]
    · apply le_of_lt
      apply (mul_lt_mul_iff_right₀ hN).mp
      nlinarith
  have hhalf : 3/4≤θ := by linarith [hθ.1]
  have hlow : q^2/4≤1-θ := by linarith [hθ.2]
  have hp := mul_le_mul ((mul_le_mul_iff_right₀ hN).mpr hhalf) hlow
    (by positivity : (0:ℝ)≤q^2/4) (mul_nonneg hN.le (by linarith : 0≤θ))
  refine ⟨hθ,?_⟩
  change 1≤(N:ℝ)*θ*(1-θ)
  nlinarith

/-- An explicit unconditional tail for the actual count law. Its q⁴ exponent
 is more than enough under the source's q⁻¹=N^{o(1)} standing regime. -/
theorem initial_count_bad_mass {N : ℕ} {q : ℝ}
    (hq : q∈Set.Ioc 0 (1/2:ℝ)) (hscale : 8≤(N:ℝ)*q^2) :
    (boundedCountLaw (le_refl N) (1-primitiveErasure q)
      (primitiveRetention_mem ⟨hq.1,by linarith [hq.2]⟩)).expect
      (fun l => if initialCountAdmissible N q l then 0 else 1) ≤
    2*Real.exp (-(N:ℝ)*q^4/64) := by
  let p := 1-primitiveErasure q
  have hp : p∈Set.Icc 0 1 := primitiveRetention_mem ⟨hq.1,by linarith [hq.2]⟩
  have ht : q^2/8∈Set.Icc (0:ℝ) 1 := ⟨by positivity,by nlinarith [hq.1,hq.2]⟩
  have H := binomialMass_abs_tail N (a:=(N:ℝ)*q^2/4) hp ht
  have he : -(q^2/8)*((N:ℝ)*q^2/4)+(N:ℝ)*(q^2/8)^2= -(N:ℝ)*q^4/64 := by ring
  rw [he] at H
  apply le_trans _ H
  rw [Finset.sum_filter,←Fin.sum_univ_eq_sum_range]
  apply Finset.sum_le_sum
  intro l _
  change binomialMass N p l.val*(if initialCountAdmissible N q l then 0 else 1)≤_
  have hn := binomialMass_nonneg N l.val hp
  by_cases hl : initialCountAdmissible N q l
  · rw [ite_eq_left hl,mul_zero]
    split_ifs <;> positivity
  · rw [ite_eq_right hl,mul_one,ite_eq_left]
    exact le_of_not_gt (fun h => hl (initialCountAdmissible_of_near hq hscale l (by simpa [p,primitiveErasure] using h)))

/-- The true bad metadata mass is charged without changing any conditional
 law or requiring an unproved concentration conclusion. -/
theorem initial_metadata_bad_mass {Side : Type*} [Fintype Side] {J N : ℕ}
    (M : PairedMechanisms Side J) {q ω : ℝ}
    (hq : q∈Set.Ioc 0 (1/2:ℝ)) (hscale : 8≤(N:ℝ)*q^2)
    (hw : ∀i,M.hiddenWeight i=ω) (hp : ω^2∈Set.Icc 0 1) :
    (initialMetadataLaw M N ⟨hq.1,by linarith [hq.2]⟩).expect
      (fun z => if initialMetadataGood q ω z then 0 else 1) ≤
    2*Real.exp (-(N:ℝ)*q^4/64)+Real.exp (-(J:ℝ)*ω^4/16) := by
  calc
    _ ≤ (initialMetadataLaw M N ⟨hq.1,by linarith [hq.2]⟩).expect
        (fun z => (if initialCountAdmissible N q z.2 then 0 else 1)+
          (if (PairedMechanisms.hiddenCount z.1:ℝ)<(J:ℝ)*ω^2/2 then 1 else 0)) := by
      apply FiniteLaw.expect_mono
      intro z
      have he : (PairedMechanisms.hiddenCount z.1:ℝ)=∑i,(hiddenTrial (z.1 i).1:ℝ) := by
        simp only [PairedMechanisms.hiddenCount,Nat.cast_sum]
      unfold initialMetadataGood
      rw [←he]
      split_ifs <;> simp_all
    _ ≤ _ := by
      simp only [FiniteLaw.expect_add,initialMetadataLaw,FiniteLaw.expect_prod]
      apply add_le_add
      · exact (M.reports.expect_mono (fun _ => initial_count_bad_mass hq hscale)).trans (by rw [FiniteLaw.expect_const])
      · convert M.hiddenCount_small hw hp using 1
        congr 1
        funext a
        split_ifs <;> simp [FiniteLaw.expect,FiniteLaw.total]

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical

def initialSignedPatternCap (J u m r s : ℕ) (q ω : ℝ) (k : Fin r → GapDifference) : ℝ :=
  if ∃a,k=linearPattern a then
    initialPrefactorCap u m r 1 q*periodCentralSumConstant u r*hiddenSignedL2Bound J s ω
  else initialPrefactorCap u m r (∑h,(k h).order) q*
    periodBoundedSumConstant u r (2*(2^s))*hiddenUnsignedL2Bound J s ω

def initialPurePatternCap (J u m r s : ℕ) (q ω : ℝ) (k : Fin r → GapDifference) : ℝ :=
  if ∃a,k=linearPattern a then
    initialPrefactorCap u m r 1 q*periodCentralSumConstant u r*hiddenSignedL2Bound J s ω
  else initialPrefactorCap u m r (∑h,(k h).order) q*
    periodCentralSumConstant u r*hiddenUnsignedL2Bound J s ω

theorem initial_signed_pattern_cap {J : ℕ} (d : Fin J → Option Bool) (c : ℤ)
    (u m r s : ℕ) (k : Fin r → GapDifference) {q θ ω : ℝ}
    (hq : q∈Set.Ioc 0 (1/2:ℝ)) (hθ : θ∈Set.Icc (1-q^2) (1-q^2/4))
    (hh : (J:ℝ)*ω^2/2≤∑i,(hiddenTrial (d i):ℝ)) :
    signedPatternBound u m r s (posteriorAnchorSeries c d) θ k ≤
      initialSignedPatternCap J u m r s q ω k := by
  unfold signedPatternBound initialSignedPatternCap
  split_ifs
  · apply mul_le_mul
    · exact mul_le_mul_of_nonneg_right (initial_prefactor_bound u m r 1 hq hθ)
        (by unfold periodCentralSumConstant; positivity)
    · exact posteriorAnchorSeries_signed_L2 d c s ω hh
    · exact seriesL2Sq_nonneg _
    · exact mul_nonneg (initialPrefactorCap_nonneg _ _ _ _ _) (by unfold periodCentralSumConstant; positivity)
  · apply mul_le_mul
    · exact mul_le_mul_of_nonneg_right (initial_prefactor_bound u m r _ hq hθ)
        (by unfold periodBoundedSumConstant; positivity)
    · exact posteriorAnchorSeries_unsigned_L2 d c s ω hh
    · exact seriesL2Sq_nonneg _
    · exact mul_nonneg (initialPrefactorCap_nonneg _ _ _ _ _) (by unfold periodBoundedSumConstant; positivity)

theorem initial_pure_pattern_cap {J : ℕ} (d : Fin J → Option Bool) (c : ℤ)
    (u m r s : ℕ) (k : Fin r → GapDifference) {q θ ω : ℝ}
    (hq : q∈Set.Ioc 0 (1/2:ℝ)) (hθ : θ∈Set.Icc (1-q^2) (1-q^2/4))
    (hh : (J:ℝ)*ω^2/2≤∑i,(hiddenTrial (d i):ℝ)) :
    purePatternBound u m r s (posteriorAnchorSeries c d) θ k ≤
      initialPurePatternCap J u m r s q ω k := by
  unfold purePatternBound initialPurePatternCap
  split_ifs
  · apply mul_le_mul
    · exact mul_le_mul_of_nonneg_right (initial_prefactor_bound u m r 1 hq hθ)
        (by unfold periodCentralSumConstant; positivity)
    · exact posteriorAnchorSeries_signed_L2 d c s ω hh
    · exact seriesL2Sq_nonneg _
    · exact mul_nonneg (initialPrefactorCap_nonneg _ _ _ _ _) (by unfold periodCentralSumConstant; positivity)
  · apply mul_le_mul
    · exact mul_le_mul_of_nonneg_right (initial_prefactor_bound u m r _ hq hθ)
        (by unfold periodCentralSumConstant; positivity)
    · exact posteriorAnchorSeries_unsigned_L2 d c s ω hh
    · exact seriesL2Sq_nonneg _
    · exact mul_nonneg (initialPrefactorCap_nonneg _ _ _ _ _) (by unfold periodCentralSumConstant; positivity)

def initialSignedDegreeCap (J u m r s : ℕ) (q ω : ℝ) : ℝ :=
  if r=0 then 0 else
    8*(Fintype.card (Fin r → GapDifference):ℝ)*
      (∑k : Fin r → GapDifference,if Odd (firstDifferenceCount k) then
        initialSignedPatternCap J u m r s q ω k else 0)+initialRankTailCap u m r

def initialPureDegreeCap (J u m r s : ℕ) (q ω : ℝ) : ℝ :=
  if r=0 then 0 else
    2*(Fintype.card (Fin r → GapDifference):ℝ)*
      (∑k : Fin r → GapDifference,if k=unchangedPattern r then 0 else
        initialPurePatternCap J u m r s q ω k)+initialRankTailCap u m r

theorem initial_signed_degree_cap {J u m l : ℕ} (d : Fin J → Option Bool) (c : ℤ) (r s : ℕ)
    {q θ ω : ℝ} (hq : q∈Set.Ioc 0 (1/2:ℝ)) (hθ : θ∈Set.Icc (1-q^2) (1-q^2/4))
    (hl : l≤u*m) (hmean : ((u*m:ℕ):ℝ)*θ=l) (hv : 1≤((u*m:ℕ):ℝ)*θ*(1-θ))
    (hh : (J:ℝ)*ω^2/2≤∑i,(hiddenTrial (d i):ℝ)) :
    signedInitialDegreeBound u m r s (posteriorAnchorSeries c d) θ l ≤
      initialSignedDegreeCap J u m r s q ω := by
  unfold signedInitialDegreeBound initialSignedDegreeCap
  split_ifs
  · exact le_rfl
  · apply add_le_add
    · apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro k _
      split_ifs
      · exact initial_signed_pattern_cap d c u m r s k hq hθ hh
      · exact le_rfl
    · exact initial_rank_tail_bound r (initial_theta_variance hq hθ).1 hl hmean hv

theorem initial_pure_degree_cap {J u m l : ℕ} (d : Fin J → Option Bool) (c : ℤ) (r s : ℕ)
    {q θ ω : ℝ} (hq : q∈Set.Ioc 0 (1/2:ℝ)) (hθ : θ∈Set.Icc (1-q^2) (1-q^2/4))
    (hl : l≤u*m) (hmean : ((u*m:ℕ):ℝ)*θ=l) (hv : 1≤((u*m:ℕ):ℝ)*θ*(1-θ))
    (hh : (J:ℝ)*ω^2/2≤∑i,(hiddenTrial (d i):ℝ)) :
    initialPureDegreeBound u m r s (posteriorAnchorSeries c d) θ l ≤
      initialPureDegreeCap J u m r s q ω := by
  unfold initialPureDegreeBound initialPureDegreeCap
  split_ifs
  · exact le_rfl
  · apply add_le_add
    · apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro k _
      split_ifs
      · exact le_rfl
      · exact initial_pure_pattern_cap d c u m r s k hq hθ hh
    · exact initial_rank_tail_bound r (initial_theta_variance hq hθ).1 hl hmean hv

/-- Scalar budgets independent of every actual report and count. The finite
 signed-pattern restriction is retained to preserve its three-difference gain. -/
def initialSignedCap (J u m R s : ℕ) (q ω w : ℝ) : ℝ :=
  (∑r∈Finset.range R,w^(2*r)*initialSignedDegreeCap J u m r s q ω)+
    4*(initialMomentRatio u m q w)^R/(1-initialMomentRatio u m q w)

def initialPureCap (J u m R s : ℕ) (q ω w : ℝ) : ℝ :=
  (∑r∈Finset.range R,w^(2*r)*initialPureDegreeCap J u m r s q ω)+
    4*(initialMomentRatio u m q w)^R/(1-initialMomentRatio u m q w)

theorem initial_signed_budget_cap {J u m l : ℕ} (d : Fin J → Option Bool) (c : ℤ) (R s : ℕ)
    {q θ ω w : ℝ} (hq : q∈Set.Ioc 0 (1/2:ℝ)) (hθ : θ∈Set.Icc (1-q^2) (1-q^2/4))
    (hl : l≤u*m) (hmean : ((u*m:ℕ):ℝ)*θ=l) (hv : 1≤((u*m:ℕ):ℝ)*θ*(1-θ))
    (hh : (J:ℝ)*ω^2/2≤∑i,(hiddenTrial (d i):ℝ)) :
    initialSignedBudget u m l R s (posteriorAnchorSeries c d) θ q w ≤
      initialSignedCap J u m R s q ω w := by
  unfold initialSignedBudget initialSignedCap
  apply add_le_add _ le_rfl
  apply Finset.sum_le_sum
  intro r _
  exact mul_le_mul_of_nonneg_left (initial_signed_degree_cap d c r s hq hθ hl hmean hv hh)
    (by rw [pow_mul]; positivity)

theorem initial_pure_budget_cap {J u m l : ℕ} (d : Fin J → Option Bool) (c : ℤ) (R s : ℕ)
    {q θ ω w : ℝ} (hq : q∈Set.Ioc 0 (1/2:ℝ)) (hθ : θ∈Set.Icc (1-q^2) (1-q^2/4))
    (hl : l≤u*m) (hmean : ((u*m:ℕ):ℝ)*θ=l) (hv : 1≤((u*m:ℕ):ℝ)*θ*(1-θ))
    (hh : (J:ℝ)*ω^2/2≤∑i,(hiddenTrial (d i):ℝ)) :
    initialPureBudget u m l R s (posteriorAnchorSeries c d) θ q w ≤
      initialPureCap J u m R s q ω w := by
  unfold initialPureBudget initialPureCap
  apply add_le_add _ le_rfl
  apply Finset.sum_le_sum
  intro r _
  exact mul_le_mul_of_nonneg_left (initial_pure_degree_cap d c r s hq hθ hl hmean hv hh)
    (by rw [pow_mul]; positivity)

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical

def OracleTracePair.weaken {q E V E' V' : ℝ} {x y : List Bool} {k : ℕ}
    (C : OracleTracePair q x y k E V) (hE : E ≤ E') (hV : V ≤ V') :
    OracleTracePair q x y k E' V' :=
  { C with
    first_simulation := fun F hF => (C.first_simulation F hF).trans hE
    second_simulation := fun F hF => (C.second_simulation F hF).trans hE
    moment := C.moment.trans hV }

def initialErrorCap (J K m k : ℕ) (q ω w : ℝ) : ℝ :=
  Real.sqrt (6*(4*(initialMomentRatio K m q w/(1-initialMomentRatio K m q w)))^k)+
    (2*Real.exp (-((K*m:ℕ):ℝ)*q^4/64)+Real.exp (-(J:ℝ)*ω^4/16))

/-- Both required initial comparisons are genuine approximate complete-trace
 oracles. The metadata budgets have been eliminated: only explicit finite
 scalar bounds and literal period geometry remain to be instantiated. -/
theorem actual_initial_oracles {J K m R : ℕ}
    (hK : 0 < K) (hm : 128 ≤ m) (hKm : K ≤ m) (hR : 0 < R)
    (off : Fin m) (hi : 1 ≤ off.val ∧ off.val+1 < m)
    (hoff : |(off.val:ℝ)-(m:ℝ)/2| ≤ 2)
    (hsafe : SafeTaggedTuple (periodSlot (u:=K) (fun _ => off)))
    (a : ℤ) (s k : ℕ) (hk : 1 ≤ k) {q w V W : ℝ}
    (hq : q∈Set.Ioc 0 (1/2:ℝ))
    (hseed : 16 ≤ q^3*(m:ℝ)) (hcount : 8 ≤ ((K*m:ℕ):ℝ)*q^2)
    (ha : (J*initialSideCount q m+J:ℕ) ≤ a)
    (ha' : a+(2^s:ℕ) ≤ (J*initialSideCount q m+K:ℕ))
    (hleft : (K:ℝ)/3 ≤ 2*((a-(J*initialSideCount q m:ℕ):ℤ)-J)+1)
    (hright : (K:ℝ)/3 ≤ 2*K-(2*((a-(J*initialSideCount q m:ℕ):ℤ)+(2:ℝ)^s)+1))
    (hM : ((2*(2^s):ℕ):ℝ) < (K:ℝ)/(3*(R+1:ℝ)))
    (hw : w=((6*(2*k:ℕ):ℝ)*(2/q)))
    (hscale : initialMomentRatio K m q w ≤ 1/2)
    (hclip : Real.sqrt (6*(4*(initialMomentRatio K m q w/(1-initialMomentRatio K m q w)))^k) ≤ 1/2)
    (hV : 0 ≤ V) (hW : 0 ≤ W)
    (hSV : 64*initialSignedCap J K m R s q (initialOverlapLower q) w ≤ V)
    (hPW : 64*initialPureCap J K m R s q (initialOverlapLower q) w ≤ W) :
    Nonempty (OracleTracePair q
      (motifPeriodWord off hi (J*(2*initialSideCount q m+1)+K) s a (-1))
      (motifPeriodWord off hi (J*(2*initialSideCount q m+1)+K) s a 1) k
      (initialErrorCap J K m k q (initialOverlapLower q) w) V) ∧
    Nonempty (OracleTracePair q
      (pureAtomRun (initialPeriod m off.val) (J*(2*initialSideCount q m+1)+K))
      (motifPeriodWord off hi (J*(2*initialSideCount q m+1)+K) s a 1) k
      (initialErrorCap J K m k q (initialOverlapLower q) w) W) := by
  let t := initialSideCount q m
  let ω := initialOverlapLower q
  let c : ℤ := a-(J*t:ℕ)
  have hω : 0 < ω := initialOverlapLower_pos q
  have hω1 : ω < 1/8 := initialOverlapLower_lt_eighth hq.1
  have hqi : q∈Set.Ioo 0 1 := ⟨hq.1,by linarith [hq.2]⟩
  have hqc : q∈Set.Icc 0 1 := ⟨hq.1.le,hqi.2.le⟩
  let u := pureAtomRun (initialPeriod m off.val) t
  let v := pureAtomRun (initialPeriod m off.val) (t+1)
  let N := max u.length v.length
  have hu : u.length ≤ N := le_max_left _ _
  have hv : v.length ≤ N := le_max_right _ _
  have hov : ω ≤ listTraceOverlap q hqc u v := initial_pure_trace_overlap hq (by omega)
    hseed off (by linarith)
  let M : PairedMechanisms (BoundedTrace N) J := tracePairedMechanisms hqc hω
    (fun _ => u) (fun _ => v) N (fun _ => hu) (fun _ => hv) (fun _ => hov)
  have hfirst (i : Fin J) : SimulatesTrace q (M.first i) Subtype.val u :=
    listTraceLaw_simulates q hqc u N hu
  have hsecond (i : Fin J) : SimulatesTrace q (M.second i) Subtype.val v :=
    listTraceLaw_simulates q hqc v N hv
  have htail := initial_metadata_bad_mass M hq hcount (fun _ => rfl)
    (show ω^2∈Set.Icc (0:ℝ) 1 from ⟨sq_nonneg _,by nlinarith⟩)
  have hsigned (z : InitialMetadata (BoundedTrace N) J (K*m))
      (hz : initialMetadataGood q ω z) :
      64*initialSignedBudget K m z.2.val R s (posteriorAnchorSeries c (fun i => (z.1 i).1))
        ((z.2.val:ℝ)/(K*m:ℕ)) q w ≤ V := by
    apply le_trans _ hSV
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    exact initial_signed_budget_cap _ c R s hq hz.1.1 (by have H:=z.2.isLt; omega)
      (mul_div_cancel₀ _ (by exact_mod_cast (Nat.mul_ne_zero (by omega : K≠0) (by omega : m≠0))))
      hz.1.2 hz.2
  have hpure (z : InitialMetadata (BoundedTrace N) J (K*m))
      (hz : initialMetadataGood q ω z) :
      64*initialPureBudget K m z.2.val R s (posteriorAnchorSeries c (fun i => (z.1 i).1))
        ((z.2.val:ℝ)/(K*m:ℕ)) q w ≤ W := by
    apply le_trans _ hPW
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    exact initial_pure_budget_cap _ c R s hq hz.1.1 (by have H:=z.2.isLt; omega)
      (mul_div_cancel₀ _ (by exact_mod_cast (Nat.mul_ne_zero (by omega : K≠0) (by omega : m≠0))))
      hz.1.2 hz.2
  have hsim (τ : ℝ) := initial_sigma_simulates M t s a τ off hi hsafe hqi
    Subtype.val hfirst hsecond ha ha'
  have hp := initial_pure_sigma_simulates (K:=K) M t off hqi Subtype.val hfirst hsecond
  obtain ⟨S⟩ := initial_sigma_clipped_exists M hK hm hKm hR off hi hoff hsafe c s k hk
    hleft hright hq hM hw hscale hclip hV hsigned
  obtain ⟨P⟩ := initial_pure_sigma_clipped_exists M hK hm hKm hR off hi hoff hsafe c s k hk
    hleft hright hq hw hscale hclip hW hpure
  constructor
  · obtain ⟨O⟩ := S.tracePair (decodeInitialObservation Subtype.val) (hsim (-1)) (hsim 1)
    exact ⟨O.weaken (add_le_add le_rfl htail) le_rfl⟩
  · obtain ⟨O⟩ := P.tracePair (decodeInitialObservation Subtype.val) hp (hsim 1)
    exact ⟨O.weaken (add_le_add le_rfl htail) le_rfl⟩

end TraceReconstruction

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
