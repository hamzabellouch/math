import OAI.NumberTheory.PiExponent.Ampleness.ReesExceptional

namespace OAI

namespace PiExponentSeshadri.ReesGrading
noncomputable section
variable {R : Type} [CommRing R] (I : Ideal R)

theorem exceptionalLineBundle_sheaf_eq :
    (exceptionalLineBundle I).sheaf = IdealModule.closedModule (exceptionalIdeal I) := rfl

end
end PiExponentSeshadri.ReesGrading

end OAI
