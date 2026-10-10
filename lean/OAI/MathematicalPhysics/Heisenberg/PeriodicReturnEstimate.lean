import OAI.MathematicalPhysics.Heisenberg.BootstrapMeshBounds

namespace OAI

section

noncomputable section
open scoped Classical BigOperators Fin.NatCast
open Filter Topology
namespace Heisenberg.Bootstrap
attribute [-instance] instDecidableEqFin
@[reducible] local instance retDecEq (α : Type*) : DecidableEq α := Classical.decEq α
attribute [local irreducible] Pin.pinDensity LayeredExchange.layerWeight LayeredExchange.coinWiring Heisenberg.Exposure.layerMass Heisenberg.Exposure.layerHistory Heisenberg.Cycle.MissingSet Heisenberg.Return.HasHit Heisenberg.Exposure.exposedSweep
open Heisenberg.Geometry Heisenberg.Schedule Heisenberg.SpatialFrame Heisenberg.MeshPair Heisenberg.Exposure Heisenberg.LatticeRegular Heisenberg.Cycle

theorem periodic_return_estimate (d : ℕ) (hd : 2 ≤ d) (L : ℝ) (hL : 0 ≤ L) :
    ∃ M : ℕ,∃ C≥0,∀ (p s : ℝ) (R : ℕ) (ρ : ℝ),0<p → 0<s → 1≤R →
      (2*(ρ+1/(1+(R:ℝ)))+8*C*(1+(R:ℝ))^((1:ℝ)/100)/s < p/4) →
      ∀ (B : Type) [Fintype B] [Nonempty B]
        (Λ F : Finset (Site (d+1))) (q : ℕ) [NeZero q]
        (edge : Fin q ≃ Edges (B:=B) Step Λ)
        (a₀ b₀ : ℕ → Slots (B:=B) Λ)
        (_ha₀ : ∀ j : Fin q,a₀ j=(edge j).val.1)
        (_hb₀ : ∀ j : Fin q,b₀ j=(edge j).val.2),
        8*(4*(d+1)*(Fintype.card B)^2:ℕ)*Real.exp 1*s ≤ R →
        ∀ᶠ δ in 𝓝 (0:ℝ),0<δ →
        ∀ (N Q : ℕ) (_hQ : 0<Q) (_hqQ : q≤Q) (_hdiv : Q∣N+1)
          (a b : Fin (N+1) → Slots (B:=B) Λ)
          (_hab : ∀ j : Fin (N+1),j.val%Q<q →
            a j=a₀ (j.val%Q) ∧ b j=b₀ (j.val%Q))
          (_hsite : ∀ j : Fin (N+1),q≤j.val%Q → (a j).1.val=(b j).1.val)
          (rates : Fin (N+1) → ℝ) (_hp : ∀ j,0≤rates j ∧ rates j≤1)
          (_hrate : ∀ j : Fin (N+1),j.val%Q<q → rates j=δ/2)
          (P : Set (Fin (N+1)×Slots (B:=B) Λ))
          (_hP : ∀ z,z.2.1.val∉F → z∈P)
          (t : Fin (N+1)) (T : Finset P) (J : Finset (Slots (B:=B) Λ)),
          T.image Subtype.val=Heisenberg.Serial.targetsAt N t J → J.Nonempty →
          (∀ j∈J,j.1.val∈F) → (∀ j∈J,(t,j)∈P) →
          F⊆Λ → (∀ z∈F,∀ w,Step z w → w∈Λ) →
          (∀ z u,0≤u → ((Finset.univ.filter (fun j : J=>dist j.val.1.val z≤u)).card:ℝ)≤L*(1+u)^((1:ℝ)/100)) →
          2*(⌊s/δ⌋₊+1)*Q ≤ N+1 →
          (∀ u x,(∑ c,layerMass (finRotate (N+1)) a b P rates c *
            (if ¬Regular (blocked Λ (holeCut (finRotate (N+1)) (fun i=>Equiv.swap (a i) (b i)) c P u))
              x R M (1/(100*(d+1:ℝ))) then (1:ℝ) else 0)) ≤ ρ) →
          (∑ c,layerMass (finRotate (N+1)) a b P rates c *
            returnCount (layerHistory (finRotate (N+1)) (fun i=>Equiv.swap (a i) (b i)) c) P T) ≤ p/2*J.card := by
  obtain ⟨M,C,hC,hflow⟩:=Heisenberg.Flow.indexed_prefix_leakage hd L hL
  refine ⟨M,C,hC,?_⟩
  intro p s R ρ hp hs hR1 herr B _ _ Λ F q _ edge a₀ b₀ ha₀ hb₀ hR
  let ar : ℕ → Slots (B:=B) Λ := fun j=>a₀ (q-1-j)
  let br : ℕ → Slots (B:=B) Λ := fun j=>b₀ (q-1-j)
  let er : Fin q ≃ Edges (B:=B) Step Λ := Fin.revPerm.trans edge
  have har (j : Fin q) : ar j=(er j).val.1 := by simpa [ar,er,Fin.rev,Nat.sub_sub,Nat.add_comm] using ha₀ j.rev
  have hbr (j : Fin q) : br j=(er j).val.2 := by simpa [br,er,Fin.rev,Nat.sub_sub,Nat.add_comm] using hb₀ j.rev
  let ε : ℝ:=p/(16*s*((Fintype.card (Slots (B:=B) Λ):ℝ)+1))
  have hε : 0<ε := by dsimp [ε]; positivity
  have h1 : (0:ℝ)<s/2 := by positivity
  have h2 : (0:ℝ)<s/(R+2) := by positivity
  have h3 : (0:ℝ)<p/(16*s*((q:ℝ)^2+1)) := by positivity
  filter_upwards [hflow B Λ F q edge a₀ b₀ ha₀ hb₀ ε hε,
    hflow B Λ F q er ar br har hbr ε hε,
    (eventually_le_nhds (by norm_num : (0:ℝ)<2)),eventually_le_nhds h1,
    eventually_le_nhds h2,eventually_le_nhds h3] with δ hforward hback hδ2 hδs hδR hsmall
  intro hδ N Q hQ hqQ hdiv a b hab hsite rates hrates hrate P hP t T J hTJ hJpos hJF hJP hF hframe hg hroom hbad
  let : NeZero Q := ⟨hQ.ne'⟩
  let n:=⌊s/δ⌋₊
  have hn : 0<n := (mesh_floor s δ hs hδ hδs).1
  have hnd : s/2 ≤ δ*(n:ℝ) := (mesh_floor s δ hs hδ hδs).2.1
  have hdn : (n:ℝ)*δ ≤ s := by simpa only [mul_comm] using (mesh_floor s δ hs hδ hδs).2.2
  have htail : ((n+2+R).choose R:ℝ)*(2*(4*(d+1)*(Fintype.card B)^2:ℕ)*δ)^R ≤ 1/(1+(R:ℝ)) :=
    Heisenberg.Clocks.binomial_clock_tail n R (4*(d+1)*(Fintype.card B)^2:ℕ) δ s
      (by positivity) hδ.le hs.le hR1 (round_clock_bound s δ hs hδ R hδR) hR
  have hremainder : (n:ℝ)*(ε*δ*Fintype.card (Slots (B:=B) Λ)+δ^2*q^2) ≤ p/4*J.card :=
    mesh_remainder p s δ ε hp hs hδ _ q n J.card
      (Finset.card_pos.mpr hJpos) hdn rfl hsmall
  have harith:=leakage_arithmetic p s δ C ρ
    (((n+2+R).choose R:ℝ)*(2*(4*(d+1)*(Fintype.card B)^2:ℕ)*δ)^R) n R J.card hp hs hδ hC htail hnd herr
    ((n:ℝ)*(ε*δ*Fintype.card (Slots (B:=B) Λ)+δ^2*q^2)) hremainder
  have hc (u : Fin (N+1)) : Heisenberg.Schedule.cut u Q n ≤ (n+1)*Q := by
    have hh:=warm_le (Q:=Q) u
    dsimp only [Heisenberg.Schedule.cut]
    nlinarith
  have hroom' : Heisenberg.Schedule.cut t Q n+Heisenberg.Schedule.cut (reverseIndex q t) Q n ≤ N+1 := by
    have hct:=hc t
    have hcr:=hc (reverseIndex q t)
    dsimp only [n] at hct hcr ⊢
    nlinarith
  have hret:=period_return_two_ends N q a b rates hrates P {v | v.1.val∈F} hP t T J (by with_reducible convert hTJ using 1; congr! 20) hJF
    (Heisenberg.Schedule.cut t Q n) (Heisenberg.Schedule.cut (reverseIndex q t) Q n) hroom'
    ((1-p/2)*J.card) ((1-p/2)*J.card) ?_ ?_
  · with_reducible convert hret using 1 <;> first | (solve | ring) | congr! 20
  · intro f hf hfJ hfs
    apply harith.trans
    have hh:=hforward hδ hδ2 (Fin (N+1)) (N+1) Q (finRotate (N+1)) (Equiv.refl _) (fun _=>rfl)
      hQ hqQ hdiv a b hab hsite rates hrates hrate P t J f n R ρ hn (by omega)
      hF hframe ?_ hfJ hf hfs hg ?_
    · convert hh using 1; first | rfl | (congr 2; first | rfl | exact Subsingleton.elim _ _)
    · intro c j hj
      refine ⟨?_,hJF j hj⟩
      exact fun h=>Set.disjoint_left.mp (missing_disjoint_pins _ P) h (hJP j hj)
    · intro i j
      exact hbad _ _
  · intro f hf hfJ hfs
    apply harith.trans
    have hh:=hback hδ hδ2 (Fin (N+1)) (N+1) Q (finRotate (N+1)).symm (reverseIndex q)
      (reverseIndex_next) hQ hqQ hdiv
      (a ∘ (finRotate (N+1)).symm) (b ∘ (finRotate (N+1)).symm) ?_ ?_
      (rates ∘ (finRotate (N+1)).symm) (fun j=>hrates _) ?_ P (reverseIndex q t) J f n R ρ hn (by omega)
      hF hframe ?_ hfJ hf ?_ hg ?_
    · convert hh using 1; first | rfl | (congr 2; first | rfl | exact Subsingleton.elim _ _)
    · intro j hj
      have hh:=reverse_phase_spatial hdiv (NeZero.pos q) hqQ j hj
      have hj' : q-1-j.val%Q < q := by omega
      have ht:=hab ((finRotate (N+1)).symm (reverseIndex q j)) (by rw [hh]; exact hj')
      simpa only [Function.comp_apply,hh,ar,br] using ht
    · intro j hj
      exact hsite _ (reverse_phase_completion hdiv (NeZero.pos q) hqQ j hj)
    · intro j hj
      have hh:=reverse_phase_spatial hdiv (NeZero.pos q) hqQ j hj
      exact hrate _ (by rw [hh]; omega)
    · intro c j hj
      have ht : reverseIndex q (reverseIndex q t)=t := by exact sub_sub_cancel (q : Fin (N+1)) t
      rw [ht]
      refine ⟨?_,hJF j hj⟩
      exact fun h=>Set.disjoint_left.mp (missing_disjoint_pins _ P) h (hJP j hj)
    · have ht : reverseIndex q (reverseIndex q t)=t := by exact sub_sub_cancel (q : Fin (N+1)) t
      simp only [ht,Function.comp_apply]
      convert hfs using 1
    · intro i j
      have he:=regularity_reverse (finRotate (N+1)) a b P rates
        (fun D : Set (Slots (B:=B) Λ)=>¬Regular (blocked Λ D) j.val.1.val R M (1/(100*(d+1:ℝ))))
        (reverseIndex q (run (reverseIndex q t) (cut (reverseIndex q t) Q i.val)))
      have hx:=hbad (reverseIndex q (run (reverseIndex q t) (cut (reverseIndex q t) Q i.val))) j.val.1.val
      have hz:=he.le.trans (show _≤ρ from by convert hx using 1; congr! 20)
      simp only [Function.comp_apply]
      convert hz using 1; congr! 20

end Heisenberg.Bootstrap
end
end

end OAI
