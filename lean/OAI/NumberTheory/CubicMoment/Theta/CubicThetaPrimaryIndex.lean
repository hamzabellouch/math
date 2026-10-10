import OAI.NumberTheory.CubicMoment.Theta.CubicThetaSieveSupport

namespace OAI

/-! Unique indexing of the primary theta frequencies by the original
squarefree and cube variables. There is no multiplicity factor. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

abbrev CubicThetaPrimaryPair :=
  {cd : Eisenstein × Eisenstein // primary cd.1 ∧ primary cd.2 ∧ Squarefree cd.1}

def cubicThetaPrimaryNumerator (cd : CubicThetaPrimaryPair) : Eisenstein :=
  lambdaE*cd.val.1*cd.val.2^3

lemma cubicThetaPrimaryNumerator_support (cd : CubicThetaPrimaryPair) :
    cubicThetaPrimarySupport (cubicThetaPrimaryNumerator cd) := by
  rw [cubicThetaPrimarySupport_iff]
  exact ⟨cd.val.1,cd.val.2,cd.property.1,cd.property.2.1,cd.property.2.2,rfl⟩

lemma cubicThetaPrimaryNumerator_injective : Function.Injective cubicThetaPrimaryNumerator := by
  intro cd ef he
  have hp : cd.val.1*cd.val.2^3 = ef.val.1*ef.val.2^3 := by
    apply mul_left_cancel₀ lambdaE_prime.ne_zero
    simpa only [cubicThetaPrimaryNumerator,mul_assoc] using he
  have hu := primary_squarefree_cube_unique cd.property.1 cd.property.2.1 ef.property.1
    ef.property.2.1 cd.property.2.2 ef.property.2.2 hp
  exact Subtype.ext (Prod.ext hu.1 hu.2)

def cubicThetaPrimaryIndexEquiv : CubicThetaPrimaryPair ≃ {n // cubicThetaPrimarySupport n} :=
  Equiv.ofBijective (fun cd => ⟨cubicThetaPrimaryNumerator cd,cubicThetaPrimaryNumerator_support cd⟩)
    ⟨fun _ _ h => cubicThetaPrimaryNumerator_injective (congrArg Subtype.val h),by
      rintro ⟨n,hn⟩
      obtain ⟨c,d,hc,hd,hs,he⟩ := (cubicThetaPrimarySupport_iff n).mp hn
      exact ⟨⟨(c,d),hc,hd,hs⟩,Subtype.ext he.symm⟩⟩

/-- Reindex a theta sum over S with exactly one term for each primary
squarefree-times-cube pair. -/
theorem cubicThetaPrimary_tsum (f : Eisenstein → ℂ) :
    (∑' n : Eisenstein, if cubicThetaPrimarySupport n then f n else 0) =
      ∑' cd : CubicThetaPrimaryPair, f (cubicThetaPrimaryNumerator cd) := by
  calc
    _ = ∑' n : {n // cubicThetaPrimarySupport n}, f n := by
      exact (tsum_subtype {n | cubicThetaPrimarySupport n} f).symm
    _ = _ := (cubicThetaPrimaryIndexEquiv.tsum_eq (fun n => f n)).symm

end CubicFirstMoment

end

end OAI
