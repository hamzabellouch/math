import OAI.Probability.ThorpResults.Statements

namespace OAI

namespace ThorpResults
open ThorpNine.Harmonic.Thorp.LowPlanes

theorem remaining_main :
    FrameMain ∧ InformationMain ∧ SpectrumMain ∧ SignedMain ∧
      DegreeSavingMain ∧ FullDensityMain ∧ ForwardMixingMain ∧ OptimalOrderMain := by
  exact ⟨Thorp.random_coordinate_frames_main,
    Thorp.deterministic_coordinate_information_main,
    bounded_regular_moment, signed_occurrence_moment, four_row_fixed_moment,
    fixed_sweep_density_convergence, fixed_sweep_mixing, Thorp.mixingTime_isTheta_log⟩

end ThorpResults

end OAI
