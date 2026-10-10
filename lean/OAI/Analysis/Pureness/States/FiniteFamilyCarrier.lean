import OAI.Analysis.Pureness.States.FiniteFamilyBounds
import OAI.Analysis.Pureness.Quasitrace.QuasitraceFunctionCarrier

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzTrace
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

abbrev FiniteQuasitraceCoordinates (A : Type*) [CStarAlgebra A] :=
  ∀ n : ℕ, FinMatrix A n → ℂ

def CompatibleFiniteQuasitrace.coordinates (F : CompatibleFiniteQuasitrace A) :
    FiniteQuasitraceCoordinates A := fun n => (F.level n).toFun

def normalizedFiniteQuasitraceCarrier : Set (FiniteQuasitraceCoordinates A) :=
  {g | (∀ n, g n ∈ complexQuasitraceCarrier) ∧
    (∀ n, Monotone (fun a : Positive (FinMatrix A n) => (g n a.1).re)) ∧
    g 1 1=1 ∧ ∀ n m (h : n ≤ m) x, g m (matrixInclusion h x)=g n x}

def finiteQuasitraceFromCoordinates (g : FiniteQuasitraceCoordinates A)
    (hg : g ∈ normalizedFiniteQuasitraceCarrier) : CompatibleFiniteQuasitrace A where
  level n := complexQuasitraceFromCarrier (g n) (hg.1 n)
  inclusion := hg.2.2.2 _ _

lemma CompatibleFiniteQuasitrace.coordinates_mem (F : CompatibleFiniteQuasitrace A)
    (hmono : ∀ n, Monotone (fun a : Positive (FinMatrix A n) => (F.level n a.1).re))
    (hF : F.level 1 1=1) : F.coordinates ∈ normalizedFiniteQuasitraceCarrier :=
  ⟨fun n => (F.level n).mem_carrier,hmono,hF,fun _ _ => F.inclusion⟩

theorem isClosed_normalizedFiniteQuasitraceCarrier :
    IsClosed (normalizedFiniteQuasitraceCarrier (A := A)) := by
  unfold normalizedFiniteQuasitraceCarrier
  refine IsClosed.inter ?_ (IsClosed.inter ?_ (IsClosed.inter ?_ ?_))
  · exact isClosed_forall_pointwise _ fun n =>
      isClosed_complexQuasitraceCarrier.preimage (continuous_apply n)
  · exact isClosed_forall_pointwise _ fun n =>
      isClosed_forall_pointwise _ fun a => isClosed_forall_pointwise _ fun b =>
      isClosed_forall_pointwise _ fun _ => isClosed_le
        (Complex.continuous_re.comp ((continuous_apply a.1).comp (continuous_apply n)))
        (Complex.continuous_re.comp ((continuous_apply b.1).comp (continuous_apply n)))
  · exact isClosed_eq ((continuous_apply 1).comp (continuous_apply 1)) continuous_const
  · exact isClosed_forall_pointwise _ fun n => isClosed_forall_pointwise _ fun m =>
      isClosed_forall_pointwise _ fun h => isClosed_forall_pointwise _ fun x =>
      isClosed_eq ((continuous_apply (matrixInclusion h x)).comp (continuous_apply m))
        ((continuous_apply x).comp (continuous_apply n))

theorem convex_normalizedFiniteQuasitraceCarrier :
    Convex ℝ (normalizedFiniteQuasitraceCarrier (A := A)) := by
  intro g hg k hk r s hr hs hrs
  refine ⟨fun n => convex_complexQuasitraceCarrier (hg.1 n) (hk.1 n) hr hs hrs,?_,?_,?_⟩
  · intro n a b hab
    change (((r : ℂ)*g n a.1+(s : ℂ)*k n a.1).re) ≤
      (((r : ℂ)*g n b.1+(s : ℂ)*k n b.1).re)
    simpa only [Complex.add_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
      zero_mul,sub_zero] using
      add_le_add (mul_le_mul_of_nonneg_left (hg.2.1 n hab) hr)
        (mul_le_mul_of_nonneg_left (hk.2.1 n hab) hs)
  · change (r : ℂ)*g 1 1+(s : ℂ)*k 1 1=1
    rw [hg.2.2.1,hk.2.2.1,mul_one,mul_one,← Complex.ofReal_add,hrs,Complex.ofReal_one]
  · intro n m h x
    change (r : ℂ)*g m (matrixInclusion h x)+(s : ℂ)*k m (matrixInclusion h x)=
      (r : ℂ)*g n x+(s : ℂ)*k n x
    rw [hg.2.2.2,hk.2.2.2]

theorem isCompact_normalizedFiniteQuasitraceCarrier :
    IsCompact (normalizedFiniteQuasitraceCarrier (A := A)) := by
  have hcompact : IsCompact {g : FiniteQuasitraceCoordinates A |
      ∀ (n : ℕ) (x : FinMatrix A n), g n x ∈ Metric.closedBall 0 (8*(n : ℝ)*‖x‖)} :=
    isCompact_pi_infinite fun (n : ℕ) => isCompact_pi_infinite fun (x : FinMatrix A n) =>
      isCompact_closedBall (0 : ℂ) (8*(n : ℝ)*‖x‖)
  apply hcompact.of_isClosed_subset isClosed_normalizedFiniteQuasitraceCarrier
  intro g hg n x
  rw [Metric.mem_closedBall,dist_zero_right]
  exact (finiteQuasitraceFromCoordinates g hg).norm_level_le hg.2.1 hg.2.2.1 n x
end CuntzPureness

end

end OAI
