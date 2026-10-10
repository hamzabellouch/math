import Mathlib
import OAI.Combinatorics.KServer.FiniteLaw

namespace OAI

/-! Relabel a finite metric across universes without changing the experiment,
initial labels, service constraints, optimal cost or behavior-policy horizon. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.FiniteMetricTransport
attribute [local instance] Classical.propDecidable Classical.decEq
universe u v
variable {Y:Type u} {Z:Type v}

lemma configuration_map {k:ℕ} (f:Y→Z) (s:Configuration k Y) (h:List (Y×Fin k)):
    configurationAfter (f∘s) (mapHistory f h)=f∘configurationAfter s h:=by
  induction h generalizing s with
  | nil=>rfl
  | cons a h ih=>
    simp only [mapHistory,List.map_cons,configurationAfter,List.foldl_cons]
    change configurationAfter (serve (f∘s) a.2 (f a.1)) (mapHistory f h)=
      f∘configurationAfter (serve s a.2 a.1) h
    rw [←map_serve f]
    exact ih _

lemma stronglyLazy {k:ℕ} (e:Y≃Z) (s:Configuration k Y) (A:Policy k Z)
    (hA:StronglyLazy (e∘s) A):StronglyLazy s (retractPolicy e A):=by
  intro h r hi j hj
  apply hA (mapHistory e h) (e r)
  · obtain ⟨i,hi⟩:=hi
    refine ⟨i,?_⟩
    rw [configuration_map]
    exact congrArg e hi
  · rw [configuration_map]
    exact fun he=>hj (e.injective he)

variable [MetricSpace Y] [MetricSpace Z]
lemma cost {k:ℕ} (e:Y≃Z) (he:Isometry e.symm) (s:Configuration k Y) (A:Policy k Z) (σ:List Y):
    expectedCost (retractPolicy e A) s σ=expectedCost A (e∘s) (σ.map e):=by
  have hh:=expectedCost_retract e e.symm e.apply_symm_apply he A (e∘s) (σ.map e)
  simpa [Function.comp_def] using hh

variable [Fintype Y] [Fintype Z]
omit [MetricSpace Y] [MetricSpace Z] in
def lawOn {H:ℕ} (e:Y≃Z) (law:FiniteDistribution (Fin H→Y)):FiniteDistribution (Fin H→Z):=
  ⟨fun σ=>law.val (e.symm∘σ),fun σ=>law.property.1 _,by
    calc
      (∑ σ:Fin H→Z,law.val (e.symm∘σ))=∑ σ:Fin H→Y,law.val σ:=by
        exact Fintype.sum_equiv (Equiv.arrowCongr (Equiv.refl (Fin H)) e.symm)
          _ _ (fun _=>rfl)
      _=1:=law.property.2⟩

omit [MetricSpace Y] [MetricSpace Z] in
lemma sum_lawOn {H:ℕ} (e:Y≃Z) (law:FiniteDistribution (Fin H→Y)) (f:(Fin H→Z)→ℝ):
    (∑ σ:Fin H→Z,(lawOn e law).val σ*f σ)=∑ σ:Fin H→Y,law.val σ*f (e∘σ):=by
  apply Fintype.sum_equiv (Equiv.arrowCongr (Equiv.refl (Fin H)) e.symm)
  intro σ
  dsimp only [lawOn,Equiv.arrowCongr,Equiv.refl,Equiv.coe_fn_mk,Function.comp_def]
  congr 2
  funext i
  exact (e.apply_symm_apply (σ i)).symm

lemma mean_cost {k H:ℕ} (e:Y≃Z) (he:Isometry e.symm) (s:Configuration k Y)
    (A:Policy k Z) (law:FiniteDistribution (Fin H→Y)):
    (∑ σ:Fin H→Y,law.val σ*expectedCost (retractPolicy e A) s (List.ofFn σ))=
      ∑ σ:Fin H→Z,(lawOn e law).val σ*expectedCost A (e∘s) (List.ofFn σ):=by
  rw [sum_lawOn]
  apply sum_congr rfl
  intro σ _
  rw [cost e he,List.map_ofFn]

lemma mean_opt {k H:ℕ} [NeZero k] (e:Y≃Z) (he:Isometry e) (s:Configuration k Y)
    (law:FiniteDistribution (Fin H→Y)):
    (∑ σ:Fin H→Z,(lawOn e law).val σ*optimalCost (e∘s) (List.ofFn σ))=
      ∑ σ:Fin H→Y,law.val σ*optimalCost s (List.ofFn σ):=by
  rw [sum_lawOn]
  apply sum_congr rfl
  intro σ _
  simpa only [List.map_ofFn] using congrArg (fun c:ℝ=>law.val σ*c)
    (optimalCost_map e he s (List.ofFn σ))
end KServer.FiniteMetricTransport

end


/-! Unconditional finite-law theorem, with one absolute coefficient and a
law/horizon-independent inventory. Finite relabeling removes the construction's
universe-zero implementation restriction. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer
open GlobalEndpoint FiniteMetricTransport
attribute [local instance] Classical.propDecidable Classical.decEq
universe u

theorem finite_law : FiniteLawStatement.{u}:=by
  refine ⟨competitiveMultiplier,?_⟩
  intro Y mY fY _ k hk s
  have : NeZero k:=⟨by omega⟩
  let Z:=Fin (Fintype.card Y)
  let e:Y≃Z:=Fintype.equivFin Y
  let : MetricSpace Z:=e.symm.metricSpace
  have hes:Isometry e.symm:=isometry_iff_dist_eq.mpr (fun _ _=>rfl)
  have he:Isometry e:=isometry_iff_dist_eq.mpr (fun x y=>by
    change dist (e.symm (e x)) (e.symm (e y))=dist x y
    rw [e.symm_apply_apply,e.symm_apply_apply])
  have hkr:1≤(k:ℝ):=by exact_mod_cast (show 1≤k by omega)
  obtain ⟨R,hR,L,hL,hdia,hf⟩:=finite_scales Z
  obtain ⟨D,hD,hall⟩:=finite_geometric (e∘s) hkr hR hL hdia hf
  refine ⟨D,hD,?_⟩
  intro H law
  obtain ⟨A,hA,hcost⟩:=hall H (lawOn e law)
  refine ⟨retractPolicy e A,stronglyLazy e s A hA,?_⟩
  rw [mean_cost e hes s A law]
  rw [mean_opt e he s law] at hcost
  exact hcost

/-- The positive universal constant strengthens ReductionStatement. -/


def MainStatement : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (k : ℕ), 2 ≤ k →
    ∀ (X : Type u) (_ : MetricSpace X),
      (∃ e : Fin (k + 1) → X, Function.Injective e) →
      ∀ s : Configuration k X,
        ∃ A : Policy k X, ∃ B : ℝ,
          0 ≤ B ∧ (Function.Injective s → B = 0) ∧
          ∀ σ : List X,
            expectedCost A s σ ≤ C * (Real.log (k + 1)) ^ 2 * optimalCost s σ + B

theorem fully_quantified_main : MainStatement.{u}:=by
  obtain ⟨C,hC⟩:=finite_law_suffices_for_main finite_law.{u}
  refine ⟨max C 1,lt_of_lt_of_le (by norm_num : (0:ℝ)<1) (le_max_right C 1),?_⟩
  intro k hk X mX hX s
  have : NeZero k:=⟨by omega⟩
  obtain ⟨A,B,hB,hzero,hcost⟩:=hC k hk X mX hX s
  refine ⟨A,B,hB,hzero,?_⟩
  intro σ
  have hnp:0≤(Real.log ((k:ℝ)+1))^2*optimalCost s σ:=
    mul_nonneg (sq_nonneg _) (optimalCost_nonneg s σ)
  have hm:=mul_le_mul_of_nonneg_right (le_max_left C 1) hnp
  have hh:=hcost σ
  nlinarith only [hh,hm]
end KServer

end


namespace KServer
universe u
/-- A positive absolute squared-logarithmic competitive bound on arbitrary metrics,
with one causal policy for all horizons and every labeled starting configuration. -/
theorem main_theorem : MainStatement.{u} := fully_quantified_main
end KServer

end OAI
