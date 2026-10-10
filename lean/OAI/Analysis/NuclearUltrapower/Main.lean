import OAI.Analysis.NuclearUltrapower.Obstruction
import OAI.Analysis.NuclearUltrapower.CuntzNuclearity

namespace OAI

section

noncomputable section
namespace NuclearUltrapower

/-- The exact source main theorem, including the explicitly stated Cuntz O₂
corollary. Both universal C*-algebras and the genuine nuclearity of O₂ have
been constructed; the target and free ultrafilter are arbitrary. -/
theorem main_no_embedding : MainStatementWithCuntzCorollary.{0} := by
  obtain ⟨A,ι,hfull,hsep,hno⟩ := main_statement
  refine ⟨A,ι,hfull,hsep,hno,CuntzUniversal.bundled,CuntzUniversal.generator,
    CuntzUniversal.universal,?_⟩
  exact hno CuntzUniversal.bundled CuntzUniversal.nuclear

end NuclearUltrapower
end
end

end OAI
