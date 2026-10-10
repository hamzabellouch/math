import OAI.MathematicalPhysics.DefocusingNLS.Certificates.BoundaryCertificateArithmetic

namespace OAI

namespace DefocusingNLS.BoundaryCertificate

/-- Exact positivity of the first transformed boundary enclosure. -/
theorem row_zero_first_positive : positiveFirst16 (transformed 0 0 1 1) = true := by
  decide +kernel

theorem row_zero_second_positive : positiveFirst16 (transformed 0 1 10 1) = true := by decide +kernel
theorem row_zero_third_positive : positiveFirst16 (transformed 0 10 1 0) = true := by decide +kernel

theorem row_one_first_positive : positiveFirst16 (transformed 1 0 1 1) = true := by decide +kernel
theorem row_one_second_positive : positiveFirst16 (transformed 1 1 10 1) = true := by decide +kernel
theorem row_one_third_positive : positiveFirst16 (transformed 1 10 1 0) = true := by decide +kernel

theorem row_two_first_positive : positiveFirst16 (transformed 2 0 1 1) = true := by decide +kernel
theorem row_two_second_positive : positiveFirst16 (transformed 2 1 10 1) = true := by decide +kernel
theorem row_two_third_positive : positiveFirst16 (transformed 2 10 1 0) = true := by decide +kernel

theorem row_three_first_positive : positiveFirst16 (transformed 3 0 1 1) = true := by decide +kernel
theorem row_three_second_positive : positiveFirst16 (transformed 3 1 10 1) = true := by decide +kernel
theorem row_three_third_positive : positiveFirst16 (transformed 3 10 1 0) = true := by decide +kernel

end DefocusingNLS.BoundaryCertificate

end OAI
