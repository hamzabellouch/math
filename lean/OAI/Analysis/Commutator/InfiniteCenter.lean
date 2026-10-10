import Mathlib
import OAI.Analysis.Commutator.CentralCorner
import OAI.Analysis.Commutator.InfiniteDiagonalRange

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

local instance infiniteCenterDecidableEq {α : Sort*} : DecidableEq α := Classical.decEq α

open scoped InnerProductSpace ComplexOrder

namespace Kadison.InfiniteAmplification

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
lemma map_injective : Function.Injective (map (ι:=ℕ) (H:=H) (G:=H)) := by
  intro S T h
  ext x
  have he := congrArg (fun R : Space ℕ H →L[ℂ] Space ℕ H => R (lp.single 2 0 x) 0) h
  simpa only [map_apply,lp.single_apply,Pi.single_eq_same] using he

lemma map_norm (T : H →L[ℂ] H) : ‖map (ι:=ℕ) T‖=‖T‖ :=
  NonUnitalStarAlgHom.norm_map (diagonal (ι:=ℕ) (H:=H)).toNonUnitalStarAlgHom map_injective T

lemma mem_algebra (M : VonNeumannAlgebra H) (T : Space ℕ H →L[ℂ] Space ℕ H) :
    T∈algebra M ↔ ∃ a : M,map (a : H →L[ℂ] H)=T := Iff.rfl

lemma map_mem_algebra (M : VonNeumannAlgebra H) (a : H →L[ℂ] H) (ha : a∈M) :
    map (ι:=ℕ) a∈algebra M := ⟨⟨a,ha⟩,rfl⟩

lemma map_mem_center (M : VonNeumannAlgebra H) (a : H →L[ℂ] H) :
    map (ι:=ℕ) a∈CentralCorner.center (algebra M) ↔ a∈CentralCorner.center M := by
  rw [CentralCorner.mem_center,CentralCorner.mem_center]
  constructor
  · rintro ⟨⟨b,hb⟩,hc⟩
    have hba : (b:H →L[ℂ] H)=a := map_injective hb
    refine ⟨hba ▸ b.property,?_⟩
    intro c hc'
    apply map_injective
    change diagonal (ι:=ℕ) (H:=H) (c*a)=diagonal (ι:=ℕ) (H:=H) (a*c)
    rw [map_mul,map_mul]
    exact hc (map c) (map_mem_algebra M c hc')
  · rintro ⟨ha,hc⟩
    refine ⟨map_mem_algebra M a ha,?_⟩
    rintro _ ⟨b,rfl⟩
    change diagonal (ι:=ℕ) (H:=H) b.val*diagonal (ι:=ℕ) (H:=H) a=
      diagonal (ι:=ℕ) (H:=H) a*diagonal (ι:=ℕ) (H:=H) b.val
    rw [←map_mul,←map_mul,hc b b.property]

lemma center_range (M : VonNeumannAlgebra H) (T : Space ℕ H →L[ℂ] Space ℕ H)
    (hT : T∈CentralCorner.center (algebra M)) :
    ∃ a : CentralCorner.center M,map (a : H →L[ℂ] H)=T := by
  obtain ⟨a,rfl⟩ := (mem_algebra M T).mp ((CentralCorner.mem_center _ _).mp hT).1
  exact ⟨⟨a,(map_mem_center M a).mp hT⟩,rfl⟩

end Kadison.InfiniteAmplification

end

end
end

end OAI
