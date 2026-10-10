import OAI.Probability.ThorpRouting.Adaptive.Main
import OAI.Probability.ThorpRouting.Casimir.Main
import OAI.Probability.ThorpRouting.Contact.Main
import OAI.Probability.ThorpRouting.Dense.Main
import OAI.Probability.ThorpRouting.Harmonic.Main
import OAI.Probability.ThorpRouting.HighTail.Main
import OAI.Probability.ThorpRouting.Smoothing.Main
import OAI.Probability.ThorpRouting.SparseSaving.Main
import OAI.Probability.ThorpRouting.Tail.Main

namespace OAI

theorem ThorpNine.main :
    ThorpNine.Adaptive.Thorp.AdaptiveBounds.MainStatement ∧
    ThorpNine.Casimir.Thorp.CasimirBounds.MainStatement ∧
    ThorpNine.Dense.Thorp.DenseTruncation.MainStatement ∧
    ThorpNine.Contact.Thorp.SparseContact.MainStatement ∧
    ThorpNine.Harmonic.Thorp.HarmonicBounds.MainStatement ∧
    ThorpNine.Smoothing.Thorp.StrongSmoothing.MainStatement ∧
    ThorpNine.Tail.Thorp.StrongTail.MainStatement ∧
    ThorpNine.HighTail.Thorp.HighHeight.MainStatement ∧
    ThorpNine.SparseSaving.Thorp.SparseRegime.MainStatement := by
  exact ⟨ThorpNine.Adaptive.Thorp.AdaptiveBounds.adaptive_main,
    ThorpNine.Casimir.Thorp.CasimirBounds.casimir_main,
    ThorpNine.Dense.Thorp.DenseTruncation.dense_truncation,
    ThorpNine.Contact.Thorp.SparseContact.uniform_sparse_contact,
    ThorpNine.Harmonic.Thorp.HarmonicBounds.harmonic_cycle_main,
    ThorpNine.Smoothing.Thorp.StrongSmoothing.strong_smoothing,
    ThorpNine.Tail.Thorp.StrongTail.strong_tail,
    ThorpNine.HighTail.Thorp.HighHeight.high_tail,
    ThorpNine.SparseSaving.Thorp.SparseRegime.exponential_sparse_saving⟩

end OAI
