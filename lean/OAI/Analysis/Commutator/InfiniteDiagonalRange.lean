import Mathlib
import OAI.Analysis.Commutator.InfiniteAmplification

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

local instance {α : Sort*} : DecidableEq α := Classical.decEq α

open scoped InnerProductSpace Topology

namespace Kadison.InfiniteAmplification

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def block (i j : ℕ) : Space ℕ H →L[ℂ] Space ℕ H :=
  (lp.singleContinuousLinearMap ℂ (fun _ : ℕ => H) 2 i).comp (lp.evalCLM ℂ (fun _ : ℕ => H) 2 j)

omit [CompleteSpace H] in
lemma block_map_commute (T : H →L[ℂ] H) (i j : ℕ) :
    map T*block (H:=H) i j=block i j*map T := by
  ext x k
  change T (lp.single (E:=fun _ : ℕ => H) 2 i (x j) k)=lp.single (E:=fun _ : ℕ => H) 2 i (T (x j)) k
  by_cases hk : k=i <;> simp [lp.single_apply,hk]

def zeroth (T : Space ℕ H →L[ℂ] Space ℕ H) : H →L[ℂ] H :=
  (lp.evalCLM ℂ (fun _ : ℕ => H) 2 0).comp
    (T.comp (lp.singleContinuousLinearMap ℂ (fun _ : ℕ => H) 2 0))

omit [CompleteSpace H] in
lemma eq_map_of_blocks (T : Space ℕ H →L[ℂ] Space ℕ H)
    (hT : ∀ i j,block i j*T=T*block i j) : T=map (zeroth T) := by
  ext x i
  have he := congrArg (fun S : Space ℕ H →L[ℂ] Space ℕ H => S x 0) (hT 0 i)
  change lp.single (E:=fun _ : ℕ => H) 2 0 (T x i) 0=T (lp.single (E:=fun _ : ℕ => H) 2 0 (x i)) 0 at he
  change T x i=T (lp.single (E:=fun _ : ℕ => H) 2 0 (x i)) 0
  simpa only [lp.single_apply,Pi.single_eq_same] using he

lemma diagonal_bicommutant_range (M : VonNeumannAlgebra H) :
    Set.centralizer (Set.centralizer (Set.range ((diagonal (ι:=ℕ) (H:=H)).comp M.subtype)))=
      Set.range ((diagonal (ι:=ℕ) (H:=H)).comp M.subtype) := by
  apply Set.Subset.antisymm
  · intro T hT
    have hb : ∀ i j,block i j*T=T*block i j := fun i j => hT (block i j) (by
      rintro _ ⟨a,rfl⟩
      exact block_map_commute a.val i j)
    have he := eq_map_of_blocks T hb
    have hz : zeroth T∈M := by
      change zeroth T∈(M : Set (H →L[ℂ] H))
      rw [←M.centralizer_centralizer]
      intro b hb
      have hm : map b∈Set.centralizer (Set.range ((diagonal (ι:=ℕ) (H:=H)).comp M.subtype)) := by
        rintro _ ⟨a,rfl⟩
        change map (a : H →L[ℂ] H)*map b=map b*map a
        ext x i
        exact congrArg (fun R : H →L[ℂ] H => R (x i)) (hb a a.property)
      have hcomm := hT (map b) hm
      rw [he] at hcomm
      ext x
      have h := congrArg (fun R : Space ℕ H →L[ℂ] Space ℕ H => R (lp.single (E:=fun _ : ℕ => H) 2 0 x) 0) hcomm
      simpa only [mul_apply_eq_comp,map_apply,lp.single_apply,Pi.single_eq_same] using h
    exact ⟨⟨zeroth T,hz⟩,he.symm⟩
  · exact Set.subset_centralizer_centralizer

def algebra (M : VonNeumannAlgebra H) : VonNeumannAlgebra (Space ℕ H) where
  toStarSubalgebra := ((diagonal (ι:=ℕ) (H:=H)).comp M.subtype).range
  centralizer_centralizer' := diagonal_bicommutant_range M

end Kadison.InfiniteAmplification

end

end
end

end OAI
