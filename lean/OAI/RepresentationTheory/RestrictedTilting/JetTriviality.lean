import OAI.RepresentationTheory.RestrictedTilting.CompatibleJets

namespace OAI

namespace FiberFunctorProof
open scoped BigOperators Pointwise
section
variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

lemma map_binarySum (f : M →ₗ[R] N) (x y : R) (j : ℕ) (v : Fin (j+1) → M) :
    f (binarySum x y j v) = binarySum x y j (f ∘ v) := by
  simp only [binarySum_apply, map_sum, map_smul, Function.comp_apply]

lemma jetRelation_map_le (f : M →ₗ[R] N) (x y : R) (j : ℕ) :
    jetRelation x y j ≤ (jetRelation x y j).comap f := by
  rintro m ⟨v,rfl⟩
  exact ⟨f ∘ v, (map_binarySum f x y j v).symm⟩

 
def jetMap (f : M →ₗ[R] N) (x y : R) (j : ℕ) :
    (M ⧸ jetRelation (M := M) x y j) →ₗ[R] (N ⧸ jetRelation (M := N) x y j) :=
  (jetRelation (M := M) x y j).mapQ (jetRelation (M := N) x y j) f (jetRelation_map_le f x y j)

lemma jetMap_mk (f : M →ₗ[R] N) (x y : R) (j : ℕ) (m : M) :
    jetMap f x y j ((jetRelation x y j).mkQ m) = (jetRelation x y j).mkQ (f m) := rfl

 

lemma jetMap_surjective (f : M →ₗ[R] N) (x y : R)
    (h0 : ∀ n : N, ∃ m : M, n - f m ∈ pairRelation x y) (j : ℕ) :
    Function.Surjective (jetMap f x y j) := by
  suffices H : ∀ n : N, ∃ m : M, n - f m ∈ jetRelation x y j by
    intro z
    obtain ⟨n,rfl⟩ := (jetRelation (M := N) x y j).mkQ_surjective z
    obtain ⟨m,hm⟩ := H n
    refine ⟨(jetRelation x y j).mkQ m, ?_⟩
    rw [jetMap_mk, ← sub_eq_zero, ← map_sub]
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    simpa only [neg_sub] using (jetRelation x y j).neg_mem hm
  induction j with
  | zero => intro n; exact ⟨0, by rw [jetRelation_zero]; trivial⟩
  | succ j ih =>
    intro n
    obtain ⟨m, v, hv⟩ := ih n
    choose w hw using fun i => h0 (v i)
    refine ⟨m + binarySum x y j w, ?_⟩
    have he : n - f (m + binarySum x y j w) =
        binarySum x y j (v - f ∘ w) := by
      rw [map_add, map_binarySum, map_sub, hv]
      abel
    rw [he]
    exact binarySum_pairRelation x y j _ hw

 

lemma jetMap_injective (f : M →ₗ[R] N) (x y : R)
    (hx : Function.Injective (fun n : N => x • n))
    (hy : ∀ v n : N, y • v = x • n → ∃ w : N, v = x • w)
    (h0 : ∀ m : M, f m ∈ pairRelation x y → m ∈ pairRelation x y) (j : ℕ) :
    Function.Injective (jetMap f x y j) := by
  have H : ∀ j (m : M), f m ∈ jetRelation x y j → m ∈ jetRelation x y j := by
    intro j
    induction j with
    | zero => intros; rw [jetRelation_zero]; trivial
    | succ j ih =>
      intro m hm
      obtain ⟨v,rfl⟩ := ih m (jetRelation_succ_le x y j hm)
      rw [map_binarySum] at hm
      apply binarySum_pairRelation
      intro i
      exact h0 (v i) ((binarySum_mem_next_iff x y hx hy j (f ∘ v)).mp hm i)
  apply (LinearMap.ker_eq_bot (f := jetMap f x y j)).mp
  apply (LinearMap.ker_eq_bot' (f := jetMap f x y j)).mpr
  intro z hz
  obtain ⟨m,rfl⟩ := (jetRelation (M := M) x y j).mkQ_surjective z
  rw [jetMap_mk] at hz
  exact (Submodule.Quotient.mk_eq_zero _).mpr
    (H j m ((Submodule.Quotient.mk_eq_zero _).mp hz))

 

theorem jetMap_bijective (f : M →ₗ[R] N) (x y : R)
    (hx : Function.Injective (fun n : N => x • n))
    (hy : ∀ v n : N, y • v = x • n → ∃ w : N, v = x • w)
    (h0 : Function.Bijective (jetMap f x y 1)) (j : ℕ) :
    Function.Bijective (jetMap f x y j) := by
  constructor
  · apply jetMap_injective f x y hx hy
    intro m hm
    have hz : jetMap f x y 1 ((jetRelation x y 1).mkQ m) = 0 := by
      rw [jetMap_mk]
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      simpa only [jetRelation_one] using hm
    have hm0 := h0.1 (hz.trans (map_zero _).symm)
    simpa only [jetRelation_one] using (Submodule.Quotient.mk_eq_zero _).mp hm0
  · apply jetMap_surjective f x y
    intro n
    obtain ⟨z,hz⟩ := h0.2 ((jetRelation x y 1).mkQ n)
    obtain ⟨m,rfl⟩ := (jetRelation x y 1).mkQ_surjective z
    refine ⟨m, ?_⟩
    rw [jetMap_mk] at hz
    have hh : (jetRelation x y 1).mkQ (n - f m) = 0 := by rw [map_sub, hz, sub_self]
    simpa only [jetRelation_one] using (Submodule.Quotient.mk_eq_zero _).mp hh
end
end FiberFunctorProof

end OAI
