import OAI.Computability.WLIdentification.Hardness

namespace OAI

namespace WLIdentification

theorem main : EXPTIMEComplete dimensionLanguage :=
  ⟨dimensionLanguage_inEXPTIME, dimensionLanguage_hard⟩

end WLIdentification

end OAI
