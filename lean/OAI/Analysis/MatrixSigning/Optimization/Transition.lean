import Mathlib
import OAI.Analysis.MatrixSigning.Optimization.FaceStencil
import OAI.Analysis.MatrixSigning.Potential.FreezePotential
import OAI.Analysis.MatrixSigning.Optimization.MinList

namespace OAI

open Matrix

namespace CurrentKS.RationalFace
open CurrentKS.RationalSDP CurrentKS.Schedule CurrentKS.Difference CurrentKS.Descent

variable {d N : ℕ}

def transition (coords : Fin N → Fin d × Fin d → ℚ) (ν lam : ℚ)
    (x : Fin N → ℚ) : Option (Fin N → ℚ) :=
  if hn : (activeIndices x).length=0 then none else
    letI : NeZero (activeIndices x).length := ⟨hn⟩
    some (freezeAll (lam^2/ν) (extend (activeIndex x) x (faceChoice coords x ν lam)))

def uniformDrop (d N : ℕ) (ν lam : ℚ) : ℚ :=
  minList ((List.range (N+1)).map fun n =>
    let p := parameters d n ν lam
    p.a*p.s^2)

def rationalRun (coords : Fin N → Fin d × Fin d → ℚ) (ν lam : ℚ) : Fin N → ℚ :=
  run (transition coords ν lam) (fuel (uniformDrop d N ν lam)) (freezeAll (lam^2/ν) 0)

def StripCube (σ : ℚ) (x : Fin N → ℚ) : Prop :=
  (∀ i,|x i| ≤ 1) ∧ ∀ i,|x i|<1 → |x i| ≤ 1-σ

lemma freezeAll_stripCube (σ : ℚ) (x : Fin N → ℚ) (hx : ∀ i,|x i| ≤ 1) :
    StripCube σ (freezeAll σ x) :=
  ⟨freezeList_cube σ x hx _,fun i hi => (freezeAll_strip σ x i hi).le⟩

lemma StripCube.faceState {σ : ℚ} {x : Fin N → ℚ} (hx : StripCube σ x) :
    ∀ i,|faceState x i| ≤ 1-σ :=
  fun i => hx.2 (activeIndex x i) (activeIndex_interior x i)

lemma uniformDrop_pos [NeZero d] {ν lam : ℚ} (hν : 0 < ν) (hlam : 0 < lam) :
    0 < uniformDrop d N ν lam := by
  apply minList_pos
  intro q hq
  obtain ⟨n,_,rfl⟩ := List.mem_map.mp hq
  have hd : (0:ℚ) < d := by exact_mod_cast NeZero.pos d
  have hε : 0 < ν/(d:ℚ) := div_pos hν hd
  have hσ : 0 < lam^2/ν := by positivity
  have ha := threshold_pos n (ν/(d:ℚ)) hlam
  have hM := curveBudget_one_le d n hε hσ lam
  have hs := stepSize_spec ha (lt_of_lt_of_le (by norm_num : (0:ℚ)<1) hM) hσ
  change 0 < threshold n (ν/(d:ℚ)) lam*(stepSize _ _ _)^2
  exact mul_pos ha (sq_pos_of_pos hs.1)

lemma uniformDrop_le (d N n : ℕ) (ν lam : ℚ) (hn : n ≤ N) :
    uniformDrop d N ν lam ≤ (parameters d n ν lam).a*(parameters d n ν lam).s^2 := by
  apply minList_le
  apply List.mem_map.mpr
  exact ⟨n,List.mem_range.mpr (by omega),rfl⟩

noncomputable section
open CurrentKS.Hermitian CurrentKS.State CurrentKS.Variational CurrentKS.Scalar
open scoped BigOperators MatrixOrder Matrix.Norms.Frobenius

def fullPotential (coords : Fin N → Fin d × Fin d → ℚ) (ν lam : ℚ) (x : Fin N → ℚ) : ℝ :=
  potential 384 ((ν/(d:ℚ):ℚ):ℝ) (lam:ℝ) (rationalAtoms coords) (pointCast x)

lemma fullPotential_extend (coords : Fin N → Fin d × Fin d → ℚ) (base : Fin N → ℚ)
    (ν lam : ℚ) (hb : ∀ i,|base i| ≤ 1) (y : Fin (activeIndices base).length → ℚ) :
    fullPotential coords ν lam (extend (activeIndex base) base y)=
      activePotential coords base ν lam (pointCast y) := by
  have he := potential_extend (activeIndex base) (activeIndex_injective base)
    (pointCast base) (rationalAtoms coords) (real_active_outside_endpoint base hb)
    (pointCast y) ((ν/(d:ℚ):ℚ):ℝ) (lam:ℝ)
  have hc := map_extend (fun q : ℚ => (q:ℝ)) (activeIndex base) base y
  change pointCast (extend (activeIndex base) base y)=extend (activeIndex base) (pointCast base) (pointCast y) at hc
  unfold fullPotential potential
  rw [hc]
  exact he

lemma fullPotential_self (coords : Fin N → Fin d × Fin d → ℚ) (base : Fin N → ℚ)
    (ν lam : ℚ) (hb : ∀ i,|base i| ≤ 1) :
    activePotential coords base ν lam (pointCast (faceState base))=fullPotential coords ν lam base := by
  have hh := fullPotential_extend coords base ν lam hb (faceState base)
  change fullPotential coords ν lam (extend (activeIndex base) base (fun j => base (activeIndex base j)))=_ at hh
  rw [extend_self] at hh
  exact hh.symm

lemma fullPotential_freeze [NeZero d] (coords : Fin N → Fin d × Fin d → ℚ)
    (hA : ∀ i,rationalAtoms coords i∈psdCone d)
    (htr : ∑ i,Hermitian.realTrace (rationalAtoms coords i)=1)
    {ν lam : ℚ} (hν : 0 < ν) (hν1 : ν ≤ 1) (hlam : 0 ≤ lam)
    (hvar : (∑ i,sandwich (rationalAtoms coords i) (Hermitian.one : H d)) ≤
      (ν:ℝ) • (Hermitian.one : H d))
    (x : Fin N → ℚ) (hx : ∀ i,|x i| ≤ 1) :
    fullPotential coords ν lam (freezeAll (lam^2/ν) x) ≤ fullPotential coords ν lam x := by
  have hep := epsilon_spec (d:=d) hν hν1
  exact freezeList_potential (rationalAtoms coords) hA htr hν hν1 hlam hep.1 hep.2.2 hvar x hx _

theorem transition_spec [NeZero d] (coords : Fin N → Fin d × Fin d → ℚ)
    (hA : ∀ i,rationalAtoms coords i∈psdCone d)
    (hA0 : ∀ i,rationalAtoms coords i≠0)
    (hrank : ∀ i,(rationalAtoms coords i : Mat d).rank ≤ 1)
    (htr : ∑ i,Hermitian.realTrace (rationalAtoms coords i)=1)
    {ν lam : ℚ} (hν : 0 < ν) (hν1 : ν ≤ 1) (hlam : 0 < lam) (hlam1 : lam ≤ 1)
    (hvar : (∑ i,sandwich (rationalAtoms coords i) (Hermitian.one : H d)) ≤
      (ν:ℝ) • (Hermitian.one : H d))
    (x y : Fin N → ℚ) (hx : StripCube (lam^2/ν) x)
    (hs : transition coords ν lam x=some y) :
    StripCube (lam^2/ν) y ∧
      fullPotential coords ν lam y ≤ fullPotential coords ν lam x-(uniformDrop d N ν lam:ℝ) := by
  by_cases hn : (activeIndices x).length=0
  · simp [transition,hn] at hs
  · let : NeZero (activeIndices x).length := ⟨hn⟩
    have hchoice := faceChoice_spec coords x hA hA0 hrank htr hν hν1 hlam hlam1 hvar hx.1 hx.faceState
    let z := extend (activeIndex x) x (faceChoice coords x ν lam)
    have he : y=freezeAll (lam^2/ν) z := by
      simpa only [transition,dite_eq_right hn,Option.some.injEq] using hs.symm
    subst y
    have hz : ∀ i,|z i| ≤ 1 := extend_cube x _ hx.1 hchoice.1
    refine ⟨freezeAll_stripCube _ z hz,?_⟩
    have hf := fullPotential_freeze coords hA htr hν hν1 hlam.le hvar z hz
    have hc : fullPotential coords ν lam z ≤ fullPotential coords ν lam x-
        3*((parameters d (activeIndices x).length ν lam).a:ℝ)*
          ((parameters d (activeIndices x).length ν lam).s:ℝ)^2/2 := by
      rw [fullPotential_extend coords x ν lam hx.1]
      simpa only [fullPotential_self coords x ν lam hx.1,mul_assoc] using hchoice.2
    have hd : (uniformDrop d N ν lam:ℝ) ≤
        ((parameters d (activeIndices x).length ν lam).a:ℝ)*
          ((parameters d (activeIndices x).length ν lam).s:ℝ)^2 := by
      exact_mod_cast uniformDrop_le d N (activeIndices x).length ν lam (activeIndices_length_le x)
    have hdp : (0:ℝ) < uniformDrop d N ν lam := by exact_mod_cast uniformDrop_pos hν hlam
    linarith

lemma terminal_vertex (coords : Fin N → Fin d × Fin d → ℚ) (ν lam : ℚ)
    (x : Fin N → ℚ) (hx : ∀ i,|x i| ≤ 1) (ht : transition coords ν lam x=none) :
    ∀ i,|x i|=1 := by
  have hn : (activeIndices x).length=0 := by
    by_contra hn
    simp only [transition,dite_eq_right hn] at ht
    contradiction
  have he : activeIndices x=[] := List.length_eq_zero_iff.mp hn
  intro i
  apply le_antisymm (hx i)
  by_contra hh
  have hh' : |x i|<1 := lt_of_not_ge hh
  have hm := (activeIndices_mem x i).mpr hh'
  exact List.not_mem_nil (he ▸ hm)

end
end CurrentKS.RationalFace

end OAI
