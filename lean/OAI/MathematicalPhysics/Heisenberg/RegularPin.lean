import OAI.MathematicalPhysics.Heisenberg.PinBridge

namespace OAI

section

noncomputable section
open scoped Classical BigOperators
attribute [-instance] instDecidableEqFin
@[reducible] local instance regDecEq (α : Type*) : DecidableEq α := Classical.decEq α
namespace Heisenberg.Exposure
open Heisenberg.Geometry Heisenberg.Schedule Heisenberg.SpatialFrame Heisenberg.MeshPair Heisenberg.LatticeRegular Heisenberg.SparseWitness Heisenberg.Cycle

attribute [local irreducible] Pin.pinDensity LayeredExchange.layerWeight LayeredExchange.coinWiring cutAdmissible layerMass layerHistory MissingSet Return.HasHit localGrowth

lemma exists_witness_scale : ∃ b : ℕ,100 ≤ b ∧ 2 ≤ (b:ℝ)^((1:ℝ)/100) := by
  obtain ⟨b,hb⟩:=exists_nat_ge (max (2^100:ℝ) 100)
  refine ⟨b,?_,?_⟩
  · exact_mod_cast (le_max_right _ _).trans hb
  · have hh:=Real.rpow_le_rpow (by positivity : (0:ℝ) ≤ 2^100)
        ((le_max_left _ _).trans hb) (by norm_num : (0:ℝ) ≤ 1/100)
    have he : ((2:ℝ)^100)^((1:ℝ)/100)=2 := by
      rw [←Real.rpow_natCast,←Real.rpow_mul (by norm_num)]
      norm_num
    rwa [he] at hh

theorem regularity_of_pin_induction (d M : ℕ) (L : ℝ) (hL : (2*(d+1):ℕ) ≤ L) :
    ∃ p₀>0,∃ C≥0,∀ (B : Type) [Fintype B] [Nonempty B]
      (Λ : Finset (Site (d+1))) (m : ℕ) (s : Equiv.Perm (Fin m))
      (a b : Fin m → Slots (B:=B) Λ) (P : Set (Fin m×Slots (B:=B) Λ))
      (rates : Fin m → ℝ) (_hrates : ∀ i,0≤rates i ∧ rates i≤1) (p : ℝ),
      0≤p → p≤p₀ →
      (∀ U : Finset (Fin m×Slots (B:=B) Λ),
        cutAdmissible (fun v : Slots (B:=B) Λ=>v.1.val) ((1:ℝ)/100) L U →
        Disjoint P (U:Set (Fin m×Slots (B:=B) Λ)) →
        (∑ c,if ∀ j∈U,¬Return.HasHit (LayeredExchange.coinWiring s a b c) P j then
          Pin.pinDensity (LayeredExchange.layerWeight rates) (LayeredExchange.coinWiring s a b) P c else 0) ≤ p^U.card) →
      ∀ t x R,(∑ c,layerMass s a b P rates c *
        (if ¬Regular (blocked Λ (holeCut s (fun i=>Equiv.swap (a i) (b i)) c P t)) x R M (1/(100*(d+1:ℝ))) then (1:ℝ) else 0)) ≤
          C*((1+(R:ℝ))^(d+1)*p^(2*(d+1))+1/(1+(R:ℝ))) := by
  obtain ⟨b,hb,hba⟩:=exists_witness_scale
  obtain ⟨p₀,hp₀,C,hC,hr⟩:=uniform_layer_regularity d M b hb ((1:ℝ)/100) L
    (1/(100*(d+1:ℝ))) 1 (by norm_num) hL hba (by positivity) (by norm_num)
  refine ⟨p₀,hp₀,C,hC,?_⟩
  intro B _ _ Λ m s a b P rates hrates p hp hpp hIH t x R
  have hcut:=cut_moment_of_induction (fun v : Slots (B:=B) Λ=>v.1.val) ((1:ℝ)/100) L s a b P rates p (by
    intro U hU hdis
    have h1:=hIH U
    have h2:=h1 hU
    have h3:=h2 hdis
    with_reducible convert h3 using 1 ; congr! 20) t
  have hh:=hr (Fin m) (Slots (B:=B) Λ) (fun v=>v.1.val) s a b P rates hrates t p hp hpp hcut x R
  simp only [layerBlocked_frame,Real.rpow_neg_one,←one_div,mul_ite,mul_one,mul_zero] at hh ⊢
  with_reducible convert hh using 1 ; congr! 20

lemma regularity_reverse {V : Type} [Fintype V] {m : ℕ} (s : Equiv.Perm (Fin m))
    (a b : Fin m → V) (P : Set (Fin m×V)) (rates : Fin m → ℝ)
    (F : Set V → Prop) (t : Fin m) :
    (∑ c,layerMass s.symm (a ∘ s.symm) (b ∘ s.symm) P (rates ∘ s.symm) c *
      if F (holeCut s.symm (fun i=>Equiv.swap (a (s.symm i)) (b (s.symm i))) c P t) then (1:ℝ) else 0)=
    ∑ c,layerMass s a b P rates c *
      if F (holeCut s (fun i=>Equiv.swap (a i) (b i)) c P t) then (1:ℝ) else 0 := by
  have he : ∀ c,holeCut s.symm (fun i=>Equiv.swap (a (s.symm i)) (b (s.symm i))) c P t=
      holeCut s (fun i=>Equiv.swap (a i) (b i)) (c ∘ s) P t := by
    intro c
    have hh:=holeCut_reverse s a b (c ∘ s) P t
    have hc : (c ∘ s) ∘ s.symm=c := by funext i; simp
    rwa [hc] at hh
  simp_rw [he]
  exact layerSum_reverse s a b P rates (fun c=>if F (holeCut s (fun i=>Equiv.swap (a i) (b i)) c P t) then 1 else 0)

end Heisenberg.Exposure
end
end

end OAI
