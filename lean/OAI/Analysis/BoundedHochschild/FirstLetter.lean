import Mathlib
import OAI.Analysis.BoundedHochschild.BlockSpans
import OAI.Analysis.BoundedHochschild.PowerRigidity

namespace OAI

/-! Finite and countable first-letter rigidity for free Haar families. -/

noncomputable section

open scoped ComplexOrder
open Filter Topology
namespace HochschildFirstLetter
noncomputable section
open Filter Topology
open scoped Polynomial ComplexOrder
open HochschildFreeSums HochschildNewtonPolar HochschildBlockSpan
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma tendsto_norm_of_span (τ : A →ₚ[ℂ] ℂ)
    (u : (r : ℕ) → FreeGroup (Fin (r+1)) →* A)
    (h1 : τ 1 = 1) (hu : ∀ r g, star (u r g) = u r g⁻¹)
    (hfree : ∀ r g, g ≠ 1 → τ (u r g) = 0)
    (htr : ∀ a b : A, τ (a*b) = τ (b*a))
    (hf : ∀ a : A, τ (star a*a) = 0 → a = 0)
    (R : A →L[ℂ] A) (a : A) (b : Bool)
    (hR : ∀ r (g : FreeGroup (Fin (r+1))), (g.toWord.map Prod.fst).Nodup →
      HochschildBlockWords.Ends b g.toWord → R (u r g) = a*u r g)
    {x : ℕ → A} (hx : x ∈ span (fun r => freeSum (u r)) b) :
    Tendsto (fun r => ‖R (x r)-a*x r‖) atTop (nhds 0) := by
  let T : A →L[ℝ] A := (R-ContinuousLinearMap.mul ℂ A a).restrictScalars ℝ
  have hT : ∀ r (g : FreeGroup (Fin (r+1))), (g.toWord.map Prod.fst).Nodup →
      HochschildBlockWords.Ends b g.toWord → T (u r g) = 0 := by
    intro r g hnodup hends
    change R (u r g)-a*u r g = 0
    rw [hR r g hnodup hends,sub_self]
  have ht := (tendsto_of_mem τ u h1 hu hfree htr hf T b hT hx).norm
  change Tendsto (fun r => ‖R (x r)-a*x r‖) atTop (nhds ‖(0:A)‖) at ht
  simpa only [norm_zero] using ht

 
lemma choose_diagonal (E : Bool → ℕ → ℕ → ℕ → ℝ) (c : ℕ → ℕ → ℝ) (C : ℕ → ℝ)
    (hE : ∀ b n k, 0 < k → Tendsto (E b n k) atTop (nhds 0))
    (hc : ∀ n, Tendsto (c n) atTop (nhds (C n))) :
    ∃ r : ℕ → ℕ, (∀ n, |c n (r n)-C n| < 1/(n+1:ℝ)) ∧
      (∀ b n k, 0 < k → k ≤ n → E b n k (r n) < 1/(n+1:ℝ)) := by
  have hex (n : ℕ) : ∃ r, |c n r-C n| < 1/(n+1:ℝ) ∧
      ∀ b k, 0 < k → k ≤ n → E b n k r < 1/(n+1:ℝ) := by
    have heps : 0 < 1/(n+1:ℝ) := by positivity
    have he : ∀ᶠ r in atTop, ∀ b k, 0 < k → k ≤ n → E b n k r < 1/(n+1:ℝ) := by
      apply eventually_all.mpr
      intro b
      have hb : ∀ᶠ r in atTop, ∀ k ∈ Finset.Icc 1 n, E b n k r < 1/(n+1:ℝ) := by
        apply (eventually_all_finset _).mpr
        intro k hk
        exact (hE b n k (Finset.mem_Icc.mp hk).1).eventually (gt_mem_nhds heps)
      filter_upwards [hb] with r hr
      intro k hk hkn
      exact hr k (Finset.mem_Icc.mpr ⟨hk,hkn⟩)
    have hd : ∀ᶠ r in atTop, |c n r-C n| < 1/(n+1:ℝ) := by
      simpa only [Real.dist_eq] using (hc n).eventually (Metric.ball_mem_nhds _ heps)
    exact (hd.and he).exists
  choose r hr using hex
  exact ⟨r,fun n => (hr n).1,fun b n k hk hkn => (hr n).2 b k hk hkn⟩

lemma diagonal_error_tendsto (E : Bool → ℕ → ℕ → ℕ → ℝ) (r : ℕ → ℕ)
    (h0 : ∀ b n k j, 0 ≤ E b n k j)
    (he : ∀ b n k, 0 < k → k ≤ n → E b n k (r n) < 1/(n+1:ℝ))
    (b : Bool) (k : ℕ) (hk : 0 < k) :
    Tendsto (fun n => E b n k (r n)) atTop (nhds 0) := by
  have hinv : Tendsto (fun n : ℕ => 1/(n+1:ℝ)) atTop (nhds 0) := by
    simpa only [Nat.cast_add,Nat.cast_one] using
      (tendsto_one_div_add_atTop_nhds_zero_nat : Tendsto (fun n : ℕ => 1/((n:ℝ)+1)) atTop (nhds 0))
  apply squeeze_zero' (Filter.Eventually.of_forall fun n => h0 b n k (r n)) _ hinv
  filter_upwards [eventually_ge_atTop k] with n hn
  exact (he b n k hk hn).le

 

theorem finite_config_rigidity
    (τ : A →ₚ[ℂ] ℂ) (u : (r : ℕ) → FreeGroup (Fin (r+1)) →* A)
    (h1 : τ 1 = 1) (hu : ∀ r g, star (u r g) = u r g⁻¹)
    (hfree : ∀ r g, g ≠ 1 → τ (u r g) = 0)
    (htr : ∀ a b : A, τ (a*b) = τ (b*a))
    (hf : ∀ a : A, τ (star a*a) = 0 → a = 0)
    (R : A →L[ℂ] A)
    (hR : ∀ x : ℕ → A, (∃ C : ℝ, ∀ r, ‖x r‖ ≤ C) →
      Tendsto (fun r => ‖τ.toPreGNS (x r)‖) atTop (nhds 0) →
      Tendsto (fun r => ‖τ.toPreGNS (R (x r))‖) atTop (nhds 0))
    (a b : A)
    (hp : ∀ r (g : FreeGroup (Fin (r+1))), (g.toWord.map Prod.fst).Nodup →
      HochschildBlockWords.Ends true g.toWord → R (u r g) = a*u r g)
    (hm : ∀ r (g : FreeGroup (Fin (r+1))), (g.toWord.map Prod.fst).Nodup →
      HochschildBlockWords.Ends false g.toWord → R (u r g) = b*u r g) : a = b := by
  classical
  rcases subsingleton_or_nontrivial A with hA | hA
  · exact Subsingleton.elim _ _
  let s : ℕ → A := fun r => freeSum (u r)
  let q : ℕ → ℕ → A := fun n r => polarApprox (s r) n
  let E : Bool → ℕ → ℕ → ℕ → ℝ := fun t n k r =>
    if t then ‖R ((q n r)^k)-a*(q n r)^k‖ else
      ‖R (star (q n r)^k)-b*star (q n r)^k‖
  let c : ℕ → ℕ → ℝ := fun n r => (τ ((1-(1/4:ℝ) • (star (s r)*s r))^(n+1))).re
  let C : ℕ → ℝ := fun n => catalanFunctional (HochschildCatalan.cutoff^(n+1))
  have hE : ∀ t n k, 0 < k → Tendsto (E t n k) atTop (nhds 0) := by
    intro t n k hk
    cases t
    · change Tendsto (fun r => ‖R (star (q n r)^k)-b*star (q n r)^k‖) _ _
      apply tendsto_norm_of_span τ u h1 hu hfree htr hf R b false hm
      exact pow_mem s false (star_mem s true (polarApprox_mem s n)) k hk
    · change Tendsto (fun r => ‖R ((q n r)^k)-a*(q n r)^k‖) _ _
      apply tendsto_norm_of_span τ u h1 hu hfree htr hf R a true hp
      exact pow_mem s true (polarApprox_mem s n) k hk
  have hc (n : ℕ) : Tendsto (c n) atTop (nhds (C n)) := by
    have h := polynomial_moments_tendsto τ s (freeSum_moments_tendsto τ u h1 hu hfree)
      (HochschildCatalan.cutoff^(n+1))
    simpa only [c,C,HochschildCatalan.cutoff,map_pow,map_sub,map_one,map_mul,
      Polynomial.aeval_C,Polynomial.aeval_X,← Algebra.smul_def] using h
  obtain ⟨r,hc',he⟩ := choose_diagonal E c C hE hc
  have hs (r : ℕ) : ‖s r‖ ≤ 2 := norm_freeSum_le_two τ (u r) h1 (hu r) (hfree r) htr hf
  have hq (n r : ℕ) : ‖q n r‖ ≤ 1 := polarApprox_norm_le_one (s r) (hs r) n
  have hE0 (t : Bool) (n k j : ℕ) : 0 ≤ E t n k j := by cases t <;> exact norm_nonneg _
  have htE (t : Bool) (k : ℕ) (hk : 0 < k) := diagonal_error_tendsto E r hE0 he t k hk
  have hinv : Tendsto (fun n : ℕ => 1/(n+1:ℝ)) atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hdef : Tendsto (fun n => (τ (1-star (q n (r n))*q n (r n))).re) atTop (nhds 0) := by
    apply squeeze_zero (fun n => (τ.map_nonneg (defect_nonneg (s (r n)) (hs (r n)) n)).1)
      (fun n => ?_) (by simpa only [add_zero] using cutoff_catalan_tendsto_zero.add hinv)
    have hle := (τ.monotone (defect_le_cutoff (s (r n)) (hs (r n)) n)).1
    have hcupper := (abs_lt.mp (hc' n)).2
    change (τ (1-star (q n (r n))*q n (r n))).re ≤ c n (r n) at hle
    change (τ (1-star (q n (r n))*q n (r n))).re ≤ C n+1/(n+1:ℝ)
    linarith
  apply HochschildMatrixDilation.contraction_power_rigidity τ h1 htr hf R hR
    (fun n => q n (r n)) (fun n => hq n (r n)) hdef a b
  · intro k hk
    apply squeeze_zero (fun n => norm_nonneg _) (fun n => HochschildRigidity.preGNS_norm_le τ h1 _)
    exact htE true k hk
  · intro k hk
    apply squeeze_zero (fun n => norm_nonneg _) (fun n => HochschildRigidity.preGNS_norm_le τ h1 _)
    exact htE false k hk

lemma toWord_map_injective {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α → β) (hf : Function.Injective f) (g : FreeGroup α) :
    (FreeGroup.map f g).toWord = g.toWord.map (fun z => (f z.1,z.2)) := by
  have hm : FreeGroup.IsReduced (g.toWord.map (fun z => (f z.1,z.2))) := by
    rw [FreeGroup.IsReduced,List.isChain_map]
    exact FreeGroup.isReduced_toWord.imp (fun a b h he => h (hf he))
  conv_lhs => rw [← (FreeGroup.mk_toWord (x:=g)),FreeGroup.map.mk,FreeGroup.toWord_mk]
  exact hm.reduce_eq

 

theorem countable_first_letter_rigidity
    (τ : A →ₚ[ℂ] ℂ) (u : FreeGroup ℕ →* A)
    (h1 : τ 1 = 1) (hu : ∀ g, star (u g) = u g⁻¹)
    (hfree : ∀ g, g ≠ 1 → τ (u g) = 0)
    (htr : ∀ a b : A, τ (a*b) = τ (b*a))
    (hf : ∀ a : A, τ (star a*a) = 0 → a = 0)
    (R : A →L[ℂ] A)
    (hR : ∀ x : ℕ → A, (∃ C : ℝ, ∀ r, ‖x r‖ ≤ C) →
      Tendsto (fun r => ‖τ.toPreGNS (x r)‖) atTop (nhds 0) →
      Tendsto (fun r => ‖τ.toPreGNS (R (x r))‖) atTop (nhds 0))
    (a b : A)
    (hw : ∀ (g : FreeGroup ℕ) i t l, g.toWord = (i,t)::l →
      (g.toWord.map Prod.fst).Nodup → R (u g) = (if t then a else b)*u g) :
    a = b := by
  let v (r : ℕ) := u.comp (FreeGroup.map (Fin.val : Fin (r+1) → ℕ))
  have hv (r : ℕ) (g : FreeGroup (Fin (r+1))) : star (v r g) = v r g⁻¹ := by
    simp only [v,MonoidHom.comp_apply,hu,map_inv]
  have hvfree (r : ℕ) (g : FreeGroup (Fin (r+1))) (hg : g ≠ 1) : τ (v r g) = 0 := by
    apply hfree
    exact fun he => hg ((FreeGroup.map_injective Fin.val_injective) (he.trans (map_one _).symm))
  have hvword (r : ℕ) (g : FreeGroup (Fin (r+1))) (t : Bool)
      (hn : (g.toWord.map Prod.fst).Nodup) (he : HochschildBlockWords.Ends t g.toWord) :
      R (v r g) = (if t then a else b)*v r g := by
    obtain ⟨⟨i,l,hl⟩,_⟩ := he
    let h : FreeGroup ℕ := FreeGroup.map Fin.val g
    have hh := toWord_map_injective Fin.val Fin.val_injective g
    apply hw h i.val t (l.map (fun z => (z.1.val,z.2)))
    · rw [hh,hl,List.map_cons]
    · rw [hh,List.map_map]
      simpa only [List.map_map,Function.comp_def] using (hn.map Fin.val_injective)
  apply finite_config_rigidity τ v h1 hv hvfree htr hf R hR a b
  · intro r g hn he
    exact hvword r g true hn he
  · intro r g hn he
    exact hvword r g false hn he

end
end HochschildFirstLetter
end

end OAI
