import Mathlib
import OAI.Combinatorics.KMedian.Geometry.RationalBundleGeometry
import OAI.Combinatorics.KMedian.Preparation.SelectedPreparationOutcome
import OAI.Combinatorics.KMedian.Preparation.RationalSupplierScan

namespace OAI


                                            
section
namespace MetricKMedian.Preparation.RationalBundles
open Finset SupplierStars RationalSuppliers
variable {f n j : ℕ} {X : Type} [PseudoMetricSpace X]

 theorem valid (F : Fin n → Finset (Fin f)) (y : Fin f → ℚ)
    (s : Fin n → X) (i : Fin f → X)
    (d : Fin n → Fin n → ℚ) (di : Fin n → Fin f → ℚ) (V : Fin n → ℚ) (M δ : ℚ)
    (hd : ∀ t u, dist (s t) (s u)=(d t u:ℝ))
    (hdi : ∀ t a, dist (s t) (i a)=(di t a:ℝ))
    (hy : ∀ a, 0 < y a) (hM : 0 < M) (hδ : 0 < δ) (hδ1 : (δ:ℝ) < 1/2)
    (hθ : 1/((M:ℝ)*(δ:ℝ)) ≤ 1/8)
    (hu : ∀ t, ∑ a ∈ F t, y a=1)
    (hv : ∀ t, ∑ a ∈ F t, y a*di t a=V t)
    (hs : ∀ t u, t ≠ u → M*max (V t) (V u) < d t u) :
    let P := bundle d di F δ;
    let A := missing d di F δ;
    (∀ t, 0 < mass y P t) ∧ Pairwise (fun t u => Disjoint (P t) (P u)) ∧
    (∀ t, 0 ≤ mass y A t) ∧ (∀ t, mass y A t ≤ 1/8) ∧
    (∀ t, mass y P t+mass y A t=1) := by
  intro P A
  let G := geometry F y s i d di V M δ hd hdi hy hM hδ hδ1 hu hv hs
  have hc : ∀ t, (mass y A t:ℝ) ≤ 1/8 := fun t => (G.small t).trans hθ
  have hu' : ∀ t, (mass y P t:ℝ)+(mass y A t:ℝ)=1 := G.unit
  refine ⟨?_,G.disjoint,?_,?_,?_⟩
  · intro t
    have h := hc t
    have h' := hu' t
    have hp : (0:ℝ) < mass y P t := by linarith only [h,h']
    exact_mod_cast hp
  · intro t
    have h := G.nonneg t
    change (0:ℝ) ≤ (mass y A t:ℝ) at h
    exact_mod_cast h
  · intro t
    apply (Rat.cast_le (K:=ℝ)).mp
    simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using hc t
  · intro t
    exact_mod_cast hu' t

def suppliers (F : Fin n → Finset (Fin f)) (y : Fin f → ℚ)
    (s : Fin n → X) (i : Fin f → X)
    (d : Fin n → Fin n → ℚ) (di : Fin n → Fin f → ℚ) (V : Fin n → ℚ) (M δ γ : ℚ)
    (hd : ∀ t u, dist (s t) (s u)=(d t u:ℝ))
    (hdi : ∀ t a, dist (s t) (i a)=(di t a:ℝ))
    (hy : ∀ a, 0 < y a) (hM : 0 < M) (hδ : 0 < δ) (hδ1 : (δ:ℝ) < 1/2)
    (hθ : 1/((M:ℝ)*(δ:ℝ)) ≤ 1/8) (hγ : 0<γ) (hγ1 : γ≤1)
    (hu : ∀ t, ∑ a ∈ F t, y a=1)
    (hv : ∀ t, ∑ a ∈ F t, y a*di t a=V t)
    (hs : ∀ t u, t ≠ u → M*max (V t) (V u) < d t u) : RationalSuppliers.Data f n :=
  let h := valid F y s i d di V M δ hd hdi hy hM hδ hδ1 hθ hu hv hs
  {y:=y, P:=bundle d di F δ, A:=missing d di F δ,
   p:=mass y (bundle d di F δ), c:=mass y (missing d di F δ), γ:=γ,
   hy:=fun a => (hy a).le, hp:=h.1, hP:=h.2.1, hm:=fun _ => rfl, hc:=fun _ => rfl,
   hc0:=h.2.2.1, hc1:=h.2.2.2.1, hunit:=h.2.2.2.2,hγ:=hγ,hγ1:=hγ1}

 theorem scan_geometry {τ : ℝ} (qR : FixedBatch.RationalParameters τ)
    (heven : Even qR.Δ) (hτ0 : 0<τ) (hτ : τ<1) (hj : 0<j)
    (F : Fin n → Finset (Fin f)) (Fj : Fin j → Finset (Fin f)) (y : Fin f → ℚ)
    (s : Fin n → X) (i : Fin f → X) (client : Fin j → X)
    (d : Fin n → Fin n → ℚ) (di : Fin n → Fin f → ℚ)
    (df : Fin f → Fin f → ℚ) (dc : Fin j → Fin f → ℚ)
    (V : Fin n → ℚ) (v : Fin j → ℚ) (rep : Fin j → Fin n) (M δ γ T₁ B : ℚ)
    (hd : ∀ t u, dist (s t) (s u)=(d t u:ℝ))
    (hdi : ∀ t a, dist (s t) (i a)=(di t a:ℝ))
    (hdf : ∀ a b, dist (i a) (i b)=(df a b:ℝ))
    (hdc : ∀ c a, dist (client c) (i a)=(dc c a:ℝ))
    (hy : ∀ a, 0 < y a) (hy1 : ∀ a, y a≤1)
    (hM : 0 < M) (hδ : 0 < δ) (hδ1 : (δ:ℝ) ≤ 1/4)
    (hθ : 1/((M:ℝ)*(δ:ℝ)) ≤ 1/8) (hγ : 0<γ) (hγ1 : γ≤1) (hT : 0<T₁)
    (hα : (M:ℝ)/((δ:ℝ)*(T₁:ℝ)) ≤ 1/4)
    (hfail : failureFactor (γ:ℝ) (qR.g:ℝ)<1)
    (hB : (∑ a, (y a:ℝ))+3*(qR.g:ℝ)+(qR.allowance:ℝ) ≤ (B:ℝ))
    (hu : ∀ t, ∑ a ∈ F t, y a=1)
    (hv : ∀ t, ∑ a ∈ F t, y a*di t a=V t)
    (hju : ∀ c, ∑ a ∈ Fj c, y a=1)
    (hjv : ∀ c, ∑ a ∈ Fj c, y a*dc c a=v c)
    (hs : ∀ t u, t ≠ u → M*max (V t) (V u) < d t u)
    (hnearest : ∀ t, ∀ a ∈ F t, ∀ b ∉ F t, di t a≤di t b)
    (hrepV : ∀ c, V (rep c)≤v c) (hrepD : ∀ c, dist (client c) (s (rep c))≤(M:ℝ)*(v c:ℝ)) :
    let D := suppliers F y s i d di V M δ γ hd hdi hy hM hδ (by linarith only [hδ1]) hθ hγ hγ1 hu hv hs;
    ∃ O : Finset (Fin f), D.scan qR df dc B=some O ∧ O.Nonempty ∧
      (O.card:ℝ)≤(B:ℝ) ∧ (Completion.Rational.score dc O:ℝ) ≤
      ((1+2/Real.exp 1+τ)/(1-τ)) *
      (max (farFactor (δ:ℝ) (1-1/((M:ℝ)*(δ:ℝ))) ((M:ℝ)/((δ:ℝ)*(T₁:ℝ))) ((M:ℝ)/(T₁:ℝ)) (γ:ℝ))
        (nearFactor (1-1/((M:ℝ)*(δ:ℝ))) ((M:ℝ)+(1+(δ:ℝ))*(T₁:ℝ)) (γ:ℝ) (qR.g:ℝ)) /
        (1-failureFactor (γ:ℝ) (qR.g:ℝ)))*(∑ c, (v c:ℝ)) := by
  intro D
  let : Nonempty (Fin j) := ⟨⟨0,hj⟩⟩
  let G := geometry F y s i d di V M δ hd hdi hy hM hδ (by linarith only [hδ1]) hu hv hs
  obtain ⟨z,hz,r,hcap,hm,hbudget,hr,hcost⟩ := selected_preparation_outcome F Fj
    (fun a => (y a:ℝ)) s client i (fun t => (V t:ℝ)) (fun c => (v c:ℝ)) rep
    (fun a => by exact_mod_cast hy a) (fun a => by exact_mod_cast hy1 a)
    (by exact_mod_cast hM) (by exact_mod_cast hδ) hδ1 (by exact_mod_cast hT) hθ hα
    qR.gpos (by exact_mod_cast hγ) (by exact_mod_cast hγ1) heven qR.unit hfail
    (fun t => by exact_mod_cast hu t) (fun c => by exact_mod_cast hju c)
    (fun t => by simp only [hdi]; exact_mod_cast hv t)
    (fun c => by simp only [hdc]; exact_mod_cast hjv c)
    (fun t a ha b hb => by simp only [hdi]; exact_mod_cast hnearest t a ha b hb)
    (fun t u htu => by simp only [hd]; exact_mod_cast hs t u htu)
    (fun c => by exact_mod_cast hrepV c) hrepD G (D.coupled qR heven)
  obtain ⟨O,hO,hOn,hOc,hOs⟩ := D.scan_feasible qR heven hτ hj df dc i client hdf hdc B
    z hz hcap hm (by
      calc
        _ ≤ ((∑ a, (y a:ℝ))+3*(qR.g:ℝ))+(qR.allowance:ℝ) := add_le_add hbudget le_rfl
        _ ≤ (B:ℝ) := hB) r hr
  refine ⟨O,hO,hOn,hOc,?_⟩
  rw [mul_assoc]
  exact hOs.trans (mul_le_mul_of_nonneg_left hcost (by
    apply div_nonneg _ (by linarith only [hτ])
    positivity))

end MetricKMedian.Preparation.RationalBundles
end

end OAI
