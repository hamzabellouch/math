import OAI.MathematicalPhysics.Heisenberg.BootstrapParameters

namespace OAI

section

noncomputable section
open scoped Classical BigOperators Fin.NatCast
open Filter Topology
attribute [-instance] instDecidableEqFin
@[reducible] local instance meshDecEq (α : Type*) : DecidableEq α := Classical.decEq α
namespace Heisenberg.Bootstrap
open Heisenberg.Geometry Heisenberg.Schedule Heisenberg.SpatialFrame Heisenberg.MeshPair Heisenberg.Exposure Heisenberg.LatticeRegular Heisenberg.Cycle Heisenberg.Pin

attribute [local irreducible] Pin.pinDensity LayeredExchange.layerWeight LayeredExchange.coinWiring Heisenberg.Exposure.layerMass Heisenberg.Exposure.layerHistory Heisenberg.Cycle.MissingSet Heisenberg.Return.HasHit Heisenberg.Exposure.exposedSweep

lemma image_testPins {X : Type*} (E : Set X) (U : Finset X) :
    (testPins E U).image Subtype.val=U := by
  ext x
  simp only [Finset.mem_image,mem_testPins]
  constructor
  · rintro ⟨i,hi,rfl⟩; exact hi
  · intro hx; exact ⟨⟨x,Or.inr hx⟩,hx,rfl⟩

theorem mesh_pin_bound (d : ℕ) (hd : 2≤d) (B : Type) [Fintype B] [Nonempty B]
    (L : ℝ) (hL : (2*(d+1):ℕ)≤L) :
    ∃ p s : ℝ,0<p ∧ p<1/4 ∧ 0<s ∧ s=p^(-(11/10:ℝ)) ∧
      ∀ (Λ F : Finset (Site (d+1))) (q : ℕ) [NeZero q]
        (edge : Fin q ≃ Edges (B:=B) Step Λ) (a₀ b₀ : ℕ → Slots (B:=B) Λ)
        (_ha₀ : ∀ j : Fin q,a₀ j=(edge j).val.1)
        (_hb₀ : ∀ j : Fin q,b₀ j=(edge j).val.2),
        ∀ᶠ δ in 𝓝 (0:ℝ),0<δ →
        ∀ (N Q : ℕ) (_hQ : 0<Q) (_hqQ : q≤Q) (_hdiv : Q∣N+1)
          (a b : Fin (N+1) → Slots (B:=B) Λ)
          (_hab : ∀ j : Fin (N+1),j.val%Q<q → a j=a₀ (j.val%Q) ∧ b j=b₀ (j.val%Q))
          (_hsite : ∀ j : Fin (N+1),q≤j.val%Q → (a j).1.val=(b j).1.val)
          (rates : Fin (N+1) → ℝ) (_hp : ∀ j,0≤rates j ∧ rates j≤1)
          (_hrate : ∀ j : Fin (N+1),j.val%Q<q → rates j=δ/2),
          F⊆Λ → (∀ z∈F,∀ w,Step z w → w∈Λ) →
          2*(⌊s/δ⌋₊+1)*Q ≤ N+1 →
          ∀ E : Set (Fin (N+1)×Slots (B:=B) Λ), (∀ z,z.2.1.val∉F → z∈E) →
          ∀ U : Finset (Fin (N+1)×Slots (B:=B) Λ),
          cutAdmissible (fun v : Slots (B:=B) Λ=>v.1.val) ((1:ℝ)/100) L U →
          Disjoint E (U:Set (Fin (N+1)×Slots (B:=B) Λ)) →
          (∑ c,if ∀ j∈U,¬Return.HasHit (LayeredExchange.coinWiring (finRotate (N+1)) a b c) E j then
            pinDensity (LayeredExchange.layerWeight rates) (LayeredExchange.coinWiring (finRotate (N+1)) a b) E c else 0) ≤ p^U.card := by
  have hL0 : 0≤L := le_trans (Nat.cast_nonneg _) hL
  obtain ⟨M,C,hC,hret⟩:=periodic_return_estimate d hd L hL0
  obtain ⟨p₀,hp₀,G,hG,hreg⟩:=regularity_of_pin_induction d M L hL
  obtain ⟨p,s,R,hp,hps,hpp,hs,hsp,hR1,_hRM,hclock,herr⟩:=
    choose_parameters (d+1) (by omega) M (4*(d+1)*(Fintype.card B)^2:ℕ) C G p₀
      (by positivity) hC hG hp₀
  refine ⟨p,s,hp,hps,hs,hsp,?_⟩
  intro Λ F q _ edge a₀ b₀ ha₀ hb₀
  let ρ : ℝ:=G*((1+(R:ℝ))^(d+1)*p^(2*(d+1))+1/(1+(R:ℝ)))
  filter_upwards [hret p s R ρ hp hs hR1 herr B Λ F q edge a₀ b₀ ha₀ hb₀ hclock] with δ hδret
  intro hδ N Q hQ hqQ hdiv a b hab hsite rates hrates hrate hF hframe hroom
  let E₀ : Set (Fin (N+1)×Slots (B:=B) Λ):={z | z.2.1.val∉F}
  let μ:=LayeredExchange.layerWeight rates
  let π:=LayeredExchange.coinWiring (finRotate (N+1)) a b
  have hμ : ∀ c,0≤μ c:=LayeredExchange.layerWeight_nonneg rates hrates
  have hpos : 0<∑ c,μ c := by
    have hsum : (∑ c,μ c)=1 := by
      with_reducible convert LayeredExchange.layerWeight_sum rates using 1
      congr! 20
    rw [hsum]
    norm_num
  have hstable : Stable (lawSymbol μ π) := by
    with_reducible convert LayeredExchange.coinWiring_stable (finRotate (N+1)) a b rates hrates using 1
    congr! 20
  have hh:=finite_pin_induction μ π hμ hpos hstable E₀
    (cutAdmissible (fun v : Slots (B:=B) Λ=>v.1.val) ((1:ℝ)/100) L) p hp.le ?_
  · intro E hE U hU hdis
    have hEE : E₀⊆E := by intro z hz; exact hE z hz
    with_reducible convert hh E hEE U hU hdis using 1
    congr! 20
  · intro E hE U hUne hU hdis hIH
    obtain ⟨t,J,rfl,hg⟩:=hU
    have hinj : Function.Injective (fun j : Slots (B:=B) Λ=>(t,j)):=fun _ _ h=>(Prod.mk.inj h).2
    have hJpos : J.Nonempty := by simpa only [Finset.image_nonempty] using hUne
    let U:=J.image (fun j=>(t,j))
    let P:=E∪(U:Set (Fin (N+1)×Slots (B:=B) Λ))
    have hdis' : Disjoint E (U:Set (Fin (N+1)×Slots (B:=B) Λ)) := by
      with_reducible convert hdis using 1
      congr! 20
    have hJP : ∀ j∈J,(t,j)∈P := by
      intro j hj
      exact Or.inr (Finset.mem_image.mpr ⟨j,hj,rfl⟩)
    have hJF : ∀ j∈J,j.1.val∈F := by
      intro j hj
      by_contra hn
      have he : (t,j)∈E := hE hn
      exact Set.disjoint_left.mp hdis' he (Finset.mem_image.mpr ⟨j,hj,rfl⟩)
    have hP : ∀ z,z.2.1.val∉F → z∈P := fun z hz=>Or.inl (hE hz)
    have hTJ : (testPins E U).image Subtype.val=Heisenberg.Serial.targetsAt N t J := by
      with_reducible convert image_testPins E U using 1
      · congr! 20
      · unfold Heisenberg.Serial.targetsAt U
        congr! 20
    have hb : ∀ u x,(∑ c,layerMass (finRotate (N+1)) a b P rates c *
      (if ¬Regular (blocked Λ (holeCut (finRotate (N+1)) (fun i=>Equiv.swap (a i) (b i)) c P u))
        x R M (1/(100*(d+1:ℝ))) then (1:ℝ) else 0))≤ρ := by
      intro u x
      have hr:=hreg B Λ (N+1) (finRotate (N+1)) a b P rates hrates p hp.le hpp ?_ u x R
      · with_reducible convert hr using 1
      · intro V hV hv
        have hv' : Disjoint (E∪((J.image (fun j=>(t,j))):Set (Fin (N+1)×Slots (B:=B) Λ))) (V:Set (Fin (N+1)×Slots (B:=B) Λ)) := by
          with_reducible convert hv using 1
        with_reducible convert hIH V hV (by with_reducible convert hv' using 1; congr! 20) using 1
        congr! 20
    have hcount:=hδret hδ N Q hQ hqQ hdiv a b hab hsite rates hrates hrate P hP t (testPins E U) J
      (by with_reducible convert hTJ using 1) hJpos hJF hJP hF hframe
      (by with_reducible convert growth_subtype _ _ _ J hg using 1) hroom (by with_reducible convert hb using 1)
    rw [returnFraction_layer]
    have hfinal : 2*((∑ c,layerMass (finRotate (N+1)) a b P rates c *
      returnCount (layerHistory (finRotate (N+1)) (fun i=>Equiv.swap (a i) (b i)) c) P (testPins E U))/U.card)≤p := by
      have hcard : U.card=J.card := Finset.card_image_of_injective _ hinj
      rw [hcard]
      have hcardpos : (0:ℝ)<J.card := by exact_mod_cast Finset.card_pos.mpr hJpos
      have hdivcount:=(div_le_iff₀ hcardpos).mpr hcount
      nlinarith
    with_reducible convert hfinal using 1
    congr! 20

end Heisenberg.Bootstrap
end
end

end OAI
