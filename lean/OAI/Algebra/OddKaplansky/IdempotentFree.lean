import OAI.Algebra.OddKaplansky.AugmentInverse

namespace OAI

universe contextUniverse1 contextUniverse2 contextUniverse3 contextUniverse4

universe portUniverse1 portUniverse2 portUniverse3 portUniverse4 portUniverse5 portUniverse6 portUniverse7

section
namespace OddKaplansky.IdempotentFree
noncomputable section
open scoped Classical BigOperators
variable {D : Type portUniverse1} {V : Type portUniverse2} [CommRing D] [sectionInstance52 : IsLocalRing D] [AddCommGroup V] [Module D V]
variable (E : V →ₗ[D] V) (hE : E ∘ₗ E = E)
include hE in
omit [IsLocalRing D] in
lemma range_fixed (x : LinearMap.range E) : E x = x := by
  obtain ⟨v,hv⟩ := x.property
  have h := LinearMap.congr_fun hE v
  simpa only [LinearMap.comp_apply,hv] using h
lemma split
    {D : Type contextUniverse1} {V : Type contextUniverse2}
    [CommRing D] [IsLocalRing D] [AddCommGroup V] [Module D V]
    (E : V →ₗ[D] V) (hE : E ∘ₗ E = E) : E.rangeRestrict.comp (LinearMap.range E).subtype = LinearMap.id := by
  ext x
  exact range_fixed E hE x
include hE in
lemma projective [Module.Free D V] : Module.Projective D (LinearMap.range E) :=
  Module.Projective.of_split (LinearMap.range E).subtype E.rangeRestrict (split E hE)
include hE in
lemma free [Module.Free D V] [Module.Finite D V] : Module.Free D (LinearMap.range E) := by
  let := projective E hE
  exact Module.free_of_flat_of_isLocalRing

section Rectangular
variable {W : Type portUniverse3} {N : Type portUniverse4} [sectionInstance54 : Fintype W] [sectionInstance53 : Fintype N]
variable (q : (N → V) ≃ₗ[D] (W → LinearMap.range E))
def J : Matrix W N (Module.End D V) := fun w n =>
  (LinearMap.range E).subtype ∘ₗ LinearMap.proj w ∘ₗ q.toLinearMap ∘ₗ LinearMap.single D (fun _ : N => V) n
def Y : Matrix N W (Module.End D V) := fun n w =>
  LinearMap.proj n ∘ₗ q.symm.toLinearMap ∘ₗ LinearMap.single D (fun _ : W => LinearMap.range E) w ∘ₗ E.rangeRestrict
omit [IsLocalRing D] in
lemma single_sum (x : N → V) : ∑ n : N, (LinearMap.single D (fun _ : N => V) n) (x n) = x := by
  ext n
  simp
omit [IsLocalRing D] in
lemma YJ
    {D : Type contextUniverse1} {V : Type contextUniverse2}
    [CommRing D] [AddCommGroup V] [Module D V]
    (E : V →ₗ[D] V) (hE : E ∘ₗ E = E)
    {W : Type contextUniverse3} {N : Type contextUniverse4} [Fintype W] [Fintype N]
    (q : (N → V) ≃ₗ[D] (W → LinearMap.range E)) : Y E q * J E q = 1 := by
  funext n n'
  apply LinearMap.ext
  intro v
  let x := q (Pi.single n' v)
  have hs : ∑ w : W, Pi.single w (x w) = x := single_sum (D := D) x
  calc
    (Y E q * J E q) n n' v = ∑ w : W, (q.symm (Pi.single w (x w))) n := by
      simp only [Matrix.mul_apply,Module.End.mul_apply,LinearMap.sum_apply,Y,J,LinearMap.comp_apply]
      apply Finset.sum_congr rfl
      intro w _
      change (q.symm (Pi.single w (E.rangeRestrict (x w : V)))) n = (q.symm (Pi.single w (x w))) n
      have hr : E.rangeRestrict (x w : V) = x w := Subtype.ext (range_fixed E hE (x w))
      rw [hr]
    _ = (q.symm (∑ w : W, Pi.single w (x w))) n := by simp only [map_sum,Finset.sum_apply]
    _ = (Pi.single n' v : N → V) n := by rw [hs]; exact congrFun (q.symm_apply_apply (Pi.single n' v)) n
    _ = (1 : Matrix N N (Module.End D V)) n n' v := by
      by_cases h : n=n'
      · subst n'; simp
      · simp [h]
omit [IsLocalRing D] in
lemma JY
    {D : Type contextUniverse1} {V : Type contextUniverse2}
    [CommRing D] [AddCommGroup V] [Module D V]
    (E : V →ₗ[D] V)
    {W : Type contextUniverse3} {N : Type contextUniverse4} [Fintype W] [Fintype N]
    (q : (N → V) ≃ₗ[D] (W → LinearMap.range E)) : J E q * Y E q = Matrix.diagonal (fun _ : W => E) := by
  funext w w'
  apply LinearMap.ext
  intro v
  let x := q.symm (Pi.single w' (E.rangeRestrict v))
  have hs : ∑ n : N, Pi.single n (x n) = x := single_sum (D := D) x
  calc
    (J E q * Y E q) w w' v = ∑ n : N, ((q (Pi.single n (x n))) w : V) := by
      simp only [Matrix.mul_apply,Module.End.mul_apply,LinearMap.sum_apply,Y,J,LinearMap.comp_apply]
      rfl
    _ = ((q (∑ n : N, Pi.single n (x n))) w : V) := by simp only [map_sum,Finset.sum_apply,Submodule.coe_sum]
    _ = (((Pi.single w' (E.rangeRestrict v) : W → LinearMap.range E)) w : V) := by rw [hs]; exact congrArg (fun f : W → LinearMap.range E => (f w : V)) (q.apply_symm_apply (Pi.single w' (E.rangeRestrict v)))
    _ = (Matrix.diagonal (fun _ : W => E)) w w' v := by
      by_cases h : w=w'
      · subst w'; simp
      · simp [h]
end Rectangular

section Dimension
variable {K : Type portUniverse5} [Field K] [Algebra K D] [Module K V] [IsScalarTower K D V]
variable [Module.Free D V] [Module.Finite D V] [Module.Finite K D]
variable {W : Type portUniverse6} {N : Type portUniverse7} [Fintype W] [Fintype N]
include hE in
lemma rectangular (hw : Fintype.card W = Module.finrank K V)
    (hn : Fintype.card N = Module.finrank K (LinearMap.range E)) :
    ∃ (J : Matrix W N (Module.End D V)) (Y : Matrix N W (Module.End D V)),
      Y*J=1 ∧ J*Y=Matrix.diagonal (fun _ : W => E) := by
  let := free E hE
  have hv := Module.finrank_mul_finrank K D V
  have he := Module.finrank_mul_finrank K D (LinearMap.range E)
  have heq : Module.finrank D (N → V) = Module.finrank D (W → LinearMap.range E) := by
    simp only [Module.finrank_pi_fintype,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    rw [hw,hn]
    nlinarith
  let q := LinearEquiv.ofFinrankEq (R := D) (N → V) (W → LinearMap.range E) heq
  exact ⟨J E q,Y E q,YJ E hE q,JY E q⟩
end Dimension
end
end OddKaplansky.IdempotentFree

end

end OAI
