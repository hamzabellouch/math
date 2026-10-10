import OAI.MathematicalPhysics.DefocusingNLS.Certificates.ExteriorCertificateRecipe

namespace OAI

/-! Exact positivity checks for the three finite exterior polynomials. -/

namespace DefocusingNLS.ExteriorCertificate

theorem diagonal_coefficients_positive :
    positiveCoefficients (realCoefficients (diagonal 270400000) 11) = true := by
  decide +kernel

theorem real_bound_coefficients_positive : positiveCoefficients realBound = true := by
  decide +kernel

theorem imaginary_bound_coefficients_positive : positiveCoefficients imaginaryBound = true := by
  decide +kernel

end DefocusingNLS.ExteriorCertificate

end OAI
