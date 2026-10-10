import OAI.MathematicalPhysics.Heisenberg.MeshRoom

namespace OAI

section
noncomputable section
open scoped Classical BigOperators Fin.NatCast Matrix Matrix.Norms.Operator
open Filter Topology
attribute [-instance] instDecidableEqFin instDecidableEqProd
@[reducible] local instance completedSurfaceDecEq (α : Type*) : DecidableEq α := Classical.decEq α
namespace Heisenberg.Surface
open Heisenberg.Geometry LatticeRegular SpatialFrame MeshPair

lemma trace_tendsto {V I : Type*} [Fintype V] {l : Filter I} {f : I → Matrix V V ℝ}
    {M : Matrix V V ℝ} (hf : Tendsto f l (𝓝 M)) :
    Tendsto (fun i=>Matrix.trace (f i)) l (𝓝 (Matrix.trace M)) := by
  exact tendsto_finsetSum _ (fun i _=>(Heat.entry i i).continuous.tendsto M |>.comp hf)

theorem completed_surface_bound (d : ℕ) (hd : 2≤d) (B : Type) [Fintype B] [Nonempty B] :
    ∃ s : ℝ,0<s ∧
      ∀ (Λ F : Finset (Site (d+1))) (_hΛ : Λ.Nonempty) (q : ℕ) [NeZero q]
        (edge : Fin q ≃ Edges (B:=B) Step Λ) (a₀ b₀ : ℕ → Slots (B:=B) Λ)
        (_ha₀ : ∀ j : Fin q,a₀ j=(edge j).val.1)
        (_hb₀ : ∀ j : Fin q,b₀ j=(edge j).val.2)
        (c : ℕ) (u v : ℕ → Slots (B:=B) Λ)
        (_huv : ∀ j,(u j).1.val=(v j).1.val)
        (_hF : F⊆Λ) (_hf : ∀ z∈F,∀ w,Step z w → w∈Λ) (t : ℝ) (_ht : 2*s<t),
        let Z:=((Finset.univ.filter (fun v : Slots (B:=B) Λ=>v.1.val∉F)).card:ℝ)
        let J:=(((Finset.range q).filter (fun j=>(a₀ j).1.val∉F ∨ (b₀ j).1.val∉F)).card:ℝ)
        let E:=NormedSpace.exp (t • ∑ j∈Finset.range q,(1/2:ℝ) • (SlotColor.matrix (Equiv.swap (a₀ j) (b₀ j))-1))
        let U:=prefixMatrix (fun j=>SlotColor.matrix (Equiv.swap (u j) (v j))) c
        Real.exp (-(Real.log 2)*(Z+2*t*J))/2*Matrix.trace (U*E)≤
          Matrix.trace (U*E*tailProjection (Slots (B:=B) Λ)) := by
  obtain ⟨s,hs,hbound⟩:=mesh_matrix_surface d hd B
  refine ⟨s,hs,?_⟩
  intro Λ F hΛ q _ edge a₀ b₀ ha₀ hb₀ c u v huv hF hf t ht Z J E U
  let Q:=q+c
  have hq : 0<q:=NeZero.pos q
  have hQ : 0<Q:=by dsimp [Q]; omega
  have ht0 : 0<t:=by linarith
  let A : ℝ → Matrix (Slots (B:=B) Λ → Bool) (Slots (B:=B) Λ → Bool) ℝ:=
    fun δ=>prefixMatrix (fun j=>colorCoin (a₀ j) (b₀ j) (δ/2)) q
  have hA : Tendsto (fun k : ℕ=>U*(A (t/(k+1:ℝ)))^(k+1)) atTop (𝓝 (U*E)) :=
    tendsto_const_nhds.mul (color_clock_limit a₀ b₀ q ht0.le)
  apply le_of_tendsto_of_tendsto
    (tendsto_const_nhds.mul (trace_tendsto hA))
    (trace_tendsto (hA.mul_const (tailProjection (Slots (B:=B) Λ))))
  have hδevent:=hbound Λ F hΛ q edge a₀ b₀ ha₀ hb₀
  have hδsmall : ∀ᶠ k : ℕ in atTop,t/(k+1:ℝ)≤2 :=
    (mesh_step_tendsto t).eventually (eventually_le_nhds (by norm_num))
  filter_upwards [(mesh_step_tendsto t).eventually hδevent,hδsmall,eventually_mesh_room hs.le ht Q] with k hk hk2 hroom
  let δ:=t/(k+1:ℝ)
  have hδ : 0<δ:=div_pos ht0 (by positivity)
  let a : Fin ((k+1)*Q) → Slots (B:=B) Λ:=fun j=>completedEndpoint a₀ u q c j.val
  let b : Fin ((k+1)*Q) → Slots (B:=B) Λ:=fun j=>completedEndpoint b₀ v q c j.val
  let rates : Fin ((k+1)*Q) → ℝ:=fun j=>completedRate δ q c k j.val
  have hab : ∀ j : Fin ((k+1)*Q),j.val%Q<q → a j=a₀ (j.val%Q) ∧ b j=b₀ (j.val%Q) := by
    intro j hj
    simp only [a,b,completedEndpoint,show q+c=Q from rfl,ite_eq_left hj,and_self]
  have hsite : ∀ j : Fin ((k+1)*Q),q≤j.val%Q → (a j).1.val=(b j).1.val := by
    intro j hj
    simp only [a,b,completedEndpoint,show q+c=Q from rfl,ite_eq_right (by omega : ¬j.val%Q<q)]
    exact huv _
  have hrate : ∀ j : Fin ((k+1)*Q),j.val%Q<q → rates j=δ/2 := by
    intro j hj
    simp only [rates,completedRate,show q+c=Q from rfl,ite_eq_left hj]
  have hh:=hk hδ ((k+1)*Q) Q (Nat.mul_pos (by omega) hQ) hQ (by dsimp [Q]; omega)
    (dvd_mul_left Q (k+1)) a b hab hsite rates
    (fun j=>completed_rate_bounds q c k j.val hδ.le hk2) hrate hF hf hroom
  let K:=Finset.univ.filter (fun j : Fin ((k+1)*Q)=>j.val%Q<q ∧ ((a j).1.val∉F ∨ (b j).1.val∉F))
  have hK : K.card=(k+1)*((Finset.range q).filter (fun j=>(a₀ j).1.val∉F ∨ (b₀ j).1.val∉F)).card := by
    have hset : K=Finset.univ.filter (fun j : Fin ((k+1)*Q)=>j.val%Q<q ∧
        ((a₀ (j.val%Q)).1.val∉F ∨ (b₀ (j.val%Q)).1.val∉F)) := by
      ext j
      simp only [K,Finset.mem_filter,Finset.mem_univ,true_and]
      by_cases hj : j.val%Q<q
      · rw [(hab j hj).1,(hab j hj).2]
      · simp only [hj,false_and]
    rw [hset]
    convert periodic_truncated_count (k+1) q Q (by dsimp [Q]; omega)
      (fun j=>(a₀ j).1.val∉F ∨ (b₀ j).1.val∉F) using 1 <;> congr! 10
  have he : 2*δ*(K.card:ℝ)=2*t*J := by
    rw [hK,Nat.cast_mul]
    dsimp only [δ,J]
    push_cast
    field_simp
  have hprod : Serial.product ((k+1)*Q) (fun j=>colorCoin (a j) (b j) (rates j))=U*(A δ)^(k+1) := by
    exact completed_product a₀ b₀ u v q c k δ
  change Real.exp (-(Real.log 2)*(Z+2*δ*(K.card:ℝ)))/2*
    Matrix.trace (Serial.product ((k+1)*Q) (fun j=>colorCoin (a j) (b j) (rates j)))≤_ at hh
  rw [he,hprod] at hh
  exact hh

end Heisenberg.Surface
end
end

end OAI
