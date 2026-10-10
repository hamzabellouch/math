import OAI.MathematicalPhysics.Transonic.Phase.MellinCoefficients
import OAI.MathematicalPhysics.Transonic.Profile.FiniteExistence
import OAI.MathematicalPhysics.Transonic.Shooting.FiniteExistence
import OAI.MathematicalPhysics.Transonic.Phase.Existence
import OAI.MathematicalPhysics.Transonic.Shooting.ExteriorSegment
import OAI.MathematicalPhysics.Transonic.Shooting.RegularLowRange
import OAI.MathematicalPhysics.Transonic.Shooting.RegularHighRange

/-!
# Relativistic transonic profiles for the septic wave equation

The global profile construction follows Buckmaster and Chen, and the phase
identities follow Shao, Wei, and Zhang. These profiles provide the relativistic
profile input in *Real-valued blowup for the defocusing septic wave equation*
by OpenAI.
-/
