import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.DivisorFamily
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.TestVacuous

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem.Specification
open OrdinaryCorrelations.SignedTrace Finset Classical
variable {S : PrimeSystem} {B τ C₀ : ℝ} {D : S.DivisorFamily B τ C₀} {h L : ℕ}

lemma orientedSubpath_refl (s : S.Specification D h L) : s.OrientedSubpath s 0 := by
  refine ⟨0,by omega,Or.inl ⟨s.offset_zero.symm,?_⟩⟩
  intro j
  simp only [zero_add,sub_zero]

lemma orientedSubpath_trans {s t u : S.Specification D h L} {x y : ℤ}
    (hst : s.OrientedSubpath t x) (htu : t.OrientedSubpath u y) :
    s.OrientedSubpath u (x+y) := by
  rcases hst with ⟨a,ha,hst | hst⟩ <;> rcases htu with ⟨b,hb,htu | htu⟩
  · obtain ⟨hx,hst⟩ := hst
    obtain ⟨hy,htu⟩ := htu
    refine ⟨a+b,by omega,Or.inl ⟨?_,?_⟩⟩
    · rw [hy,hst]
      ring
    · intro j
      rw [htu,hst]
      have hi : (⟨a+(b+j.val),by omega⟩ : Fin (s.length+1)) = ⟨a+b+j.val,by omega⟩ := by apply Fin.ext; dsimp; omega
      rw [hi]
      ring
  · obtain ⟨hx,hst⟩ := hst
    obtain ⟨hy,htu⟩ := htu
    refine ⟨a+b,by omega,Or.inr ⟨?_,?_⟩⟩
    · rw [hy,hst]
      have hi : (⟨a+(b+u.length),by omega⟩ : Fin (s.length+1)) = ⟨a+b+u.length,by omega⟩ := by apply Fin.ext; dsimp; omega
      rw [hi]
      ring
    · intro j
      rw [htu,hst]
      have hi : (⟨a+(b+u.length-j.val),by omega⟩ : Fin (s.length+1)) = ⟨a+b+u.length-j.val,by omega⟩ := by apply Fin.ext; dsimp; omega
      rw [hi]
      ring
  · obtain ⟨hx,hst⟩ := hst
    obtain ⟨hy,htu⟩ := htu
    refine ⟨a+t.length-b-u.length,by omega,Or.inr ⟨?_,?_⟩⟩
    · rw [hy,hst]
      have hi : (⟨a+t.length-b,by omega⟩ : Fin (s.length+1)) = ⟨a+t.length-b-u.length+u.length,by omega⟩ := by apply Fin.ext; dsimp; omega
      rw [hi]
      ring
    · intro j
      rw [htu,hst]
      have hi : (⟨a+t.length-(b+j.val),by omega⟩ : Fin (s.length+1)) = ⟨a+t.length-b-u.length+u.length-j.val,by omega⟩ := by apply Fin.ext; dsimp; omega
      rw [hi]
      ring
  · obtain ⟨hx,hst⟩ := hst
    obtain ⟨hy,htu⟩ := htu
    refine ⟨a+t.length-(b+u.length),by omega,Or.inl ⟨?_,?_⟩⟩
    · rw [hy,hst]
      ring
    · intro j
      rw [htu,hst]
      have hi : (⟨a+t.length-(b+u.length-j.val),by omega⟩ : Fin (s.length+1)) = ⟨a+t.length-(b+u.length)+j.val,by omega⟩ := by apply Fin.ext; dsimp; omega
      rw [hi]
      ring

lemma qualifies_transfer {s t : S.Specification D h L} {x x' z : ℤ}
    (hx : s.QualifiesAt x) (hx' : s.QualifiesAt x')
    (ht : t.primeSupport ⊆ s.primeSupport) (hy : t.QualifiesAt (x'+z)) :
    t.QualifiesAt (x+z) := by
  apply (t.qualifies_iff_residueTests x z).mpr
  intro p
  by_cases hp : (p:ℕ) ∈ t.primeSupport
  · have hsx := (s.qualifies_iff_residueTests x 0).mp (by simpa using hx) p
    have hsx' := (s.qualifies_iff_residueTests x' 0).mp (by simpa using hx') p
    have he := s.test_unique p (ht hp) 0 _ _ hsx hsx'
    rw [he]
    exact (t.qualifies_iff_residueTests x' z).mp hy p
  · exact t.test_vacuous p hp z _

theorem primitive_descent (s : S.Specification D h L) (x : ℤ) (hx : s.QualifiesAt x) :
    ∃ (t : S.Specification D h L) (z : ℤ), t.Primitive ∧
      s.OrientedSubpath t z ∧ t.primeSupport ⊆ s.primeSupport ∧ t.QualifiesAt (x+z) := by
  generalize hn : s.length=n
  induction n using Nat.strong_induction_on generalizing s x with
  | h n ih =>
    by_cases hs : s.Primitive
    · exact ⟨s,0,hs,s.orientedSubpath_refl,Subset.rfl,by simpa using hx⟩
    · have hh : ∃ (t : S.Specification D h L) (z x' : ℤ),
          t.length<s.length ∧ s.OrientedSubpath t z ∧
          t.primeSupport⊆s.primeSupport ∧ s.QualifiesAt x' ∧ t.QualifiesAt (x'+z) := by
        by_contra he
        exact hs ⟨⟨x,hx⟩,he⟩
      obtain ⟨t,z,x',hlt,hor,hsup,hsx',htx'⟩ := hh
      have htx := qualifies_transfer hx hsx' hsup htx'
      obtain ⟨u,v,hu,htor,husup,hux⟩ := ih t.length (by omega) t (x+z) htx rfl
      refine ⟨u,z+v,hu,orientedSubpath_trans hor htor,husup.trans hsup,?_⟩
      simpa only [add_assoc] using hux

lemma orientedSubpath_start {s t : S.Specification D h L} {z : ℤ}
    (hs : s.OrientedSubpath t z) : ∃ i, z=s.offset i := by
  obtain ⟨a,ha,hs | hs⟩ := hs
  · exact ⟨⟨a,by omega⟩,hs.1⟩
  · exact ⟨⟨a+t.length,by omega⟩,hs.1⟩

end OrdinaryCorrelations.GraphKernel.PrimeSystem.Specification

end

end OAI
