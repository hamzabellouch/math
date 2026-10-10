import Mathlib
import OAI.Probability.CriticalPercolation.LinearGroups.AbsoluteMatrixSpan
import OAI.Probability.CriticalPercolation.LinearGroups.AllPlaceKronecker
import OAI.Probability.CriticalPercolation.LinearGroups.ProperPadicModels
import OAI.Probability.CriticalPercolation.LinearGroups.ProjectiveEigenvalues

namespace OAI

section
noncomputable section
open Set Function Module
open scoped Classical

namespace CriticalPercolation.LinearGrowth
variable {K L T G n : Type} [Field K] [Field L] [Field T] [Group G]
variable [Fintype n] [DecidableEq n]
variable {degree : ℕ}

omit [DecidableEq n] in
lemma eigenvector_transfer (f : K →+* T) (e : L →+* T)
    (A : Matrix n n K) (B : Matrix n n L)
    (hm : ∀ i j, f (A i j)=e (B i j))
    (v : n → K) (w : n → L) (hv : ∀ i, f (v i)=e (w i))
    (a : K) (b : L) (ha : f a=e b) (hAv : A.mulVec v=a • v) : B.mulVec w=b • w := by
  have hm' : A.map f=B.map e := by ext i j; exact hm i j
  have hv' : f ∘ v=e ∘ w := funext hv
  ext i
  apply e.injective
  rw [e.map_mulVec,←hm',←hv',←f.map_mulVec,hAv]
  simp only [Pi.smul_apply,smul_eq_mul,map_mul,ha,hv]

omit [Fintype n] [DecidableEq n] in
lemma eigenvector_transfer_ne_zero (f : K →+* T) (e : L →+* T)
    (v : n → K) (w : n → L) (hv : ∀ i, f (v i)=e (w i)) (hn : v≠0) : w≠0 := by
  intro hw
  apply hn
  ext i
  apply f.injective
  simpa only [hw,Pi.zero_apply,map_zero] using hv i

lemma matrix_local_ratio_bound {K : Type} [NontriviallyNormedField K] [ProperSpace K]
    [DecidableEq G] (ρ : G →* GL n K) (hρ : StrongFullMatrixSpan ρ)
    (hg : SparseGrowth.HasPolynomialDegree G degree) (g : G)
    {v w : n → K} (hv : v≠0) (hw : w≠0) {a b : K}
    (ha : (ρ g).val.mulVec v=a • v) (hb : (ρ g).val.mulVec w=b • w) : ‖a/b‖≤1 := by
  let : Nontrivial (n → K) := ⟨⟨v,0,hv⟩⟩
  obtain ⟨S,h1,hi,hgen,hgS⟩ := (SparseGrowth.hasPolynomialDegree_iff degree).mp hg
  obtain ⟨δ,hδ,hbnd⟩ := projective_bound_of_strongFullSpan (matrixRepresentation ρ)
    (hρ.strongFullSpan ρ) S h1 hgen degree hgS
  exact eigenvalue_ratio_norm_le_one (continuousRepresentation (matrixRepresentation ρ))
    δ hδ hbnd g hv hw ha hb

lemma eigenvalue_ratio_root_of_unity_of_strongFullMatrixSpan
    [CharZero K] [Countable K] [DecidableEq G]
    (ρ : G →* GL n K) (hρ : StrongFullMatrixSpan ρ)
    (hg : SparseGrowth.HasPolynomialDegree G degree) (g : G)
    {v w : n → K} (hv : v≠0) (hw : w≠0) {a b : K}
    (ha : (ρ g).val.mulVec v=a • v) (hb : (ρ g).val.mulVec w=b • w) :
    ∃ m : ℕ, 0 < m ∧ (a/b)^m=1 := by
  have ha0 : a≠0 := by
    intro he
    have hz : (matrixRepresentation ρ g) v=(matrixRepresentation ρ g) 0 := by
      simpa only [matrixRepresentation_apply,he,zero_smul,Matrix.mulVec_zero] using ha
    exact hv ((matrixRepresentation ρ g).injective hz)
  have hb0 : b≠0 := by
    intro he
    have hz : (matrixRepresentation ρ g) w=(matrixRepresentation ρ g) 0 := by
      simpa only [matrixRepresentation_apply,he,zero_smul,Matrix.mulVec_zero] using hb
    exact hw ((matrixRepresentation ρ g).injective hz)
  apply Arithmetic.root_of_unity_of_all_places (a/b) (div_ne_zero ha0 hb0)
  · intro f
    let τ := (Matrix.GeneralLinearGroup.map f).comp ρ
    have hm : ∀ g i j, f (ρ g i j)=(RingHom.id ℂ) (τ g i j) := fun _ _ _ => rfl
    have hτ := hρ.transfer f (RingHom.id ℂ) ρ τ hm
    let v' : n → ℂ := f ∘ v
    let w' : n → ℂ := f ∘ w
    have hv' : v'≠0 := eigenvector_transfer_ne_zero f (RingHom.id ℂ) v v' (fun _ => rfl) hv
    have hw' : w'≠0 := eigenvector_transfer_ne_zero f (RingHom.id ℂ) w w' (fun _ => rfl) hw
    have ha' := eigenvector_transfer f (RingHom.id ℂ) (ρ g).val (τ g).val
      (hm g) v v' (fun _ => rfl) a (f a) rfl ha
    have hb' := eigenvector_transfer f (RingHom.id ℂ) (ρ g).val (τ g).val
      (hm g) w w' (fun _ => rfl) b (f b) rfl hb
    simpa only [map_div₀] using matrix_local_ratio_bound τ hτ hg g hv' hw' ha' hb'
  · intro p hp f
    let : Fact p.Prime := hp
    let C := AlgebraicClosure (Padic p)
    let : Group.FG G := hg.fg
    let σ := (Matrix.GeneralLinearGroup.map f).comp ρ
    let E : Finset C := {f a,f b} ∪ Finset.univ.image (f ∘ v) ∪ Finset.univ.image (f ∘ w)
    obtain ⟨L,hL,hE,τ,hτ⟩ := Arithmetic.exists_finite_padic_matrix_model p σ E
    let : FiniteDimensional (Padic p) L := hL
    let : ProperSpace L := FiniteDimensional.proper (Padic p) L
    have haL : f a∈L := hE (by simp [E])
    have hbL : f b∈L := hE (by simp [E])
    have hvL (i : n) : f (v i)∈L := hE (by simp [E,Function.comp_def])
    have hwL (i : n) : f (w i)∈L := hE (by simp [E,Function.comp_def])
    let a' : L := ⟨f a,haL⟩
    let b' : L := ⟨f b,hbL⟩
    let v' : n → L := fun i => ⟨f (v i),hvL i⟩
    let w' : n → L := fun i => ⟨f (w i),hwL i⟩
    have hm : ∀ g i j, f (ρ g i j)=L.val.toRingHom (τ g i j) := by
      intro g i j
      exact (congrArg (fun M : GL n C => M i j) (hτ g)).symm
    have hτfull := hρ.transfer f L.val.toRingHom ρ τ hm
    have hv' : v'≠0 := eigenvector_transfer_ne_zero f L.val.toRingHom v v' (fun _ => rfl) hv
    have hw' : w'≠0 := eigenvector_transfer_ne_zero f L.val.toRingHom w w' (fun _ => rfl) hw
    have ha' := eigenvector_transfer f L.val.toRingHom (ρ g).val (τ g).val
      (hm g) v v' (fun _ => rfl) a a' rfl ha
    have hb' := eigenvector_transfer f L.val.toRingHom (ρ g).val (τ g).val
      (hm g) w w' (fun _ => rfl) b b' rfl hb
    have hh := matrix_local_ratio_bound τ hτfull hg g hv' hw' ha' hb'
    change ‖((a'/b' : L) : C)‖≤1 at hh
    change ‖f (a/b)‖≤1
    simpa only [map_div₀, IntermediateField.coe_div] using hh

end CriticalPercolation.LinearGrowth
end
end

end OAI
