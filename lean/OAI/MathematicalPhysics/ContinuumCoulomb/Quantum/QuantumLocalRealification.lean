import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumLocalCoordinates

namespace OAI

/-! The realification uses one shared extra qubit and adds at most one
qubit to each interaction support. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def qmaRebitSites (S : Finset ι) : Finset (Unit ⊕ ι) :=
  insert (Sum.inl ()) (S.map Function.Embedding.inr)

def qmaRebitOnQubits (A : Matrix (ι → Fin 2) (ι → Fin 2) ℂ) :
    Matrix (Unit ⊕ ι → Fin 2) (Unit ⊕ ι → Fin 2) ℂ :=
  fun s t => qmaRebitMatrix A (s (Sum.inl ()),s ∘ Sum.inr) (t (Sum.inl ()),t ∘ Sum.inr)

omit [Fintype ι] in
theorem qmaRebitSites_card (S : Finset ι) : (qmaRebitSites S).card = S.card+1 := by
  simp [qmaRebitSites]

theorem qmaRebitOnQubits_local {S : Finset ι}
    {A : Matrix (ι → Fin 2) (ι → Fin 2) ℂ} (hA : QMALocalOn S A) :
    QMALocalOn (qmaRebitSites S) (qmaRebitOnQubits A) := by
  obtain ⟨B,rfl⟩ := hA
  let z : {i // i ∈ qmaRebitSites S} := ⟨Sum.inl (),by simp [qmaRebitSites]⟩
  let k : {i // i ∈ S} → {i // i ∈ qmaRebitSites S} := fun i =>
    ⟨Sum.inr i.val,by simp [qmaRebitSites,i.property]⟩
  refine ⟨(fun u v => qmaRebitMatrix B (u z,u ∘ k) (v z,v ∘ k)),?_⟩
  ext s t
  change qmaRebitMatrix (qmaLocalLift S B) (s (Sum.inl ()),s ∘ Sum.inr)
    (t (Sum.inl ()),t ∘ Sum.inr) =
    qmaRebitMatrix B (s (Sum.inl ()),fun i => s (Sum.inr i.val))
      (t (Sum.inl ()),fun i => t (Sum.inr i.val))*
      if (fun i : {i // i ∉ qmaRebitSites S} => s i.val) =
        (fun i : {i // i ∉ qmaRebitSites S} => t i.val) then 1 else 0
  have he : ((fun i : {i // i ∉ qmaRebitSites S} => s i.val) =
      (fun i : {i // i ∉ qmaRebitSites S} => t i.val)) ↔
      ((fun i : {i // i ∉ S} => s (Sum.inr i.val)) =
        (fun i : {i // i ∉ S} => t (Sum.inr i.val))) := by
    constructor
    · intro h
      funext i
      exact congrFun h ⟨Sum.inr i.val,by simpa [qmaRebitSites] using i.property⟩
    · intro h
      funext i
      rcases i with ⟨i,hi⟩
      cases i with
      | inl j => exact False.elim (hi (by simp [qmaRebitSites]))
      | inr j => exact congrFun h ⟨j,by simpa [qmaRebitSites] using hi⟩
  by_cases hr : (fun i : {i // i ∉ S} => s (Sum.inr i.val)) =
      (fun i : {i // i ∉ S} => t (Sum.inr i.val))
  · have hr' := he.mpr hr
    simp only [qmaRebitMatrix,qmaLocalLift_apply,
      Function.comp_apply,hr,hr',ite_true,mul_one]
  · have hr' : (fun i : {i // i ∉ qmaRebitSites S} => s i.val) ≠
        (fun i : {i // i ∉ qmaRebitSites S} => t i.val) := fun h => hr (he.mp h)
    simp only [qmaRebitMatrix,qmaLocalLift_apply,
      Function.comp_apply,hr,hr',ite_false,mul_zero,Complex.zero_re,Complex.zero_im,
      Complex.ofReal_zero,neg_zero,ite_self]

omit [Fintype ι] [DecidableEq ι] in
theorem qmaRebitOnQubits_add (A B : Matrix (ι → Fin 2) (ι → Fin 2) ℂ) :
    qmaRebitOnQubits (A+B) = qmaRebitOnQubits A+qmaRebitOnQubits B := by
  ext s t
  simp only [qmaRebitOnQubits,qmaRebitMatrix,Matrix.add_apply,Complex.add_re,Complex.add_im]
  split_ifs <;> push_cast <;> ring

omit [Fintype ι] [DecidableEq ι] in
theorem qmaRebitOnQubits_smul (a : ℝ) (A : Matrix (ι → Fin 2) (ι → Fin 2) ℂ) :
    qmaRebitOnQubits ((a:ℂ) • A) = (a:ℂ) • qmaRebitOnQubits A := by
  ext s t
  simp only [qmaRebitOnQubits,qmaRebitMatrix,Matrix.smul_apply,smul_eq_mul,
    Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,
    add_zero,sub_zero]
  split_ifs <;> push_cast <;> ring

end ContinuumCoulomb

end

end OAI
