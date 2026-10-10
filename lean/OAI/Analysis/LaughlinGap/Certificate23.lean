import Mathlib
import OAI.Analysis.LaughlinGap.CachedIntegerRows
import OAI.Analysis.LaughlinGap.FastFourKeys
import OAI.Analysis.LaughlinGap.FourTables
import OAI.Analysis.LaughlinGap.SumTable23

namespace OAI

/-! Certificate23. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators ComplexOrder
open Spin
namespace Certificate23

def keys : Fin 84 → Finset (Fin 25) := ![{0,1,2,21}, {0,1,3,20}, {0,1,4,19}, {0,1,5,18}, {0,1,6,17}, {0,1,7,16}, {0,1,8,15}, {0,1,9,14}, {0,1,10,13}, {0,1,11,12}, {0,2,3,19}, {0,2,4,18}, {0,2,5,17}, {0,2,6,16}, {0,2,7,15}, {0,2,8,14}, {0,2,9,13}, {0,2,10,12}, {0,3,4,17}, {0,3,5,16}, {0,3,6,15}, {0,3,7,14}, {0,3,8,13}, {0,3,9,12}, {0,3,10,11}, {0,4,5,15}, {0,4,6,14}, {0,4,7,13}, {0,4,8,12}, {0,4,9,11}, {0,5,6,13}, {0,5,7,12}, {0,5,8,11}, {0,5,9,10}, {0,6,7,11}, {0,6,8,10}, {0,7,8,9}, {1,2,3,18}, {1,2,4,17}, {1,2,5,16}, {1,2,6,15}, {1,2,7,14}, {1,2,8,13}, {1,2,9,12}, {1,2,10,11}, {1,3,4,16}, {1,3,5,15}, {1,3,6,14}, {1,3,7,13}, {1,3,8,12}, {1,3,9,11}, {1,4,5,14}, {1,4,6,13}, {1,4,7,12}, {1,4,8,11}, {1,4,9,10}, {1,5,6,12}, {1,5,7,11}, {1,5,8,10}, {1,6,7,10}, {1,6,8,9}, {2,3,4,15}, {2,3,5,14}, {2,3,6,13}, {2,3,7,12}, {2,3,8,11}, {2,3,9,10}, {2,4,5,13}, {2,4,6,12}, {2,4,7,11}, {2,4,8,10}, {2,5,6,11}, {2,5,7,10}, {2,5,8,9}, {2,6,7,9}, {3,4,5,12}, {3,4,6,11}, {3,4,7,10}, {3,4,8,9}, {3,5,6,10}, {3,5,7,9}, {3,6,7,8}, {4,5,6,9}, {4,5,7,8}]
def fibers : Fin 84 → Finset (FourTerm 23) := ![{⟨⟨23,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨22,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨21,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨2,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨1,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩}, {⟨⟨23,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨21,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨20,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨1,by decide⟩,(⟨0,by decide⟩,⟨3,by decide⟩)⟩}, {⟨⟨23,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨20,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨19,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨1,by decide⟩,(⟨0,by decide⟩,⟨4,by decide⟩)⟩}, {⟨⟨23,by decide⟩,(⟨5,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨19,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨18,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨1,by decide⟩,(⟨0,by decide⟩,⟨5,by decide⟩)⟩}, {⟨⟨23,by decide⟩,(⟨6,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨18,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨17,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨1,by decide⟩,(⟨0,by decide⟩,⟨6,by decide⟩)⟩}, {⟨⟨23,by decide⟩,(⟨7,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨17,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨16,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨1,by decide⟩,(⟨0,by decide⟩,⟨7,by decide⟩)⟩}, {⟨⟨23,by decide⟩,(⟨8,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨16,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨15,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨1,by decide⟩,(⟨0,by decide⟩,⟨8,by decide⟩)⟩}, {⟨⟨23,by decide⟩,(⟨9,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨15,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨14,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨1,by decide⟩,(⟨0,by decide⟩,⟨9,by decide⟩)⟩}, {⟨⟨23,by decide⟩,(⟨10,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨14,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨11,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨13,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨1,by decide⟩,(⟨0,by decide⟩,⟨10,by decide⟩)⟩}, {⟨⟨23,by decide⟩,(⟨11,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨13,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨12,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨12,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨11,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨1,by decide⟩,(⟨0,by decide⟩,⟨11,by decide⟩)⟩}, {⟨⟨22,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨21,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨19,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨2,by decide⟩,(⟨0,by decide⟩,⟨3,by decide⟩)⟩}, {⟨⟨22,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨20,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨18,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨2,by decide⟩,(⟨0,by decide⟩,⟨4,by decide⟩)⟩}, {⟨⟨22,by decide⟩,(⟨5,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨19,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨17,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨2,by decide⟩,(⟨0,by decide⟩,⟨5,by decide⟩)⟩}, {⟨⟨22,by decide⟩,(⟨6,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨18,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨16,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨2,by decide⟩,(⟨0,by decide⟩,⟨6,by decide⟩)⟩}, {⟨⟨22,by decide⟩,(⟨7,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨17,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨15,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨2,by decide⟩,(⟨0,by decide⟩,⟨7,by decide⟩)⟩}, {⟨⟨22,by decide⟩,(⟨8,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨16,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨14,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨2,by decide⟩,(⟨0,by decide⟩,⟨8,by decide⟩)⟩}, {⟨⟨22,by decide⟩,(⟨9,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨15,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨11,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨13,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨2,by decide⟩,(⟨0,by decide⟩,⟨9,by decide⟩)⟩}, {⟨⟨22,by decide⟩,(⟨10,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨14,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨12,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨12,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨2,by decide⟩,(⟨0,by decide⟩,⟨10,by decide⟩)⟩}, {⟨⟨21,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨20,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨17,by decide⟩,(⟨0,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨0,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨0,by decide⟩,⟨4,by decide⟩)⟩}, {⟨⟨21,by decide⟩,(⟨5,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨19,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨16,by decide⟩,(⟨0,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨0,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨0,by decide⟩,⟨5,by decide⟩)⟩}, {⟨⟨21,by decide⟩,(⟨6,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨18,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨15,by decide⟩,(⟨0,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨0,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨0,by decide⟩,⟨6,by decide⟩)⟩}, {⟨⟨21,by decide⟩,(⟨7,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨17,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨14,by decide⟩,(⟨0,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨0,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨0,by decide⟩,⟨7,by decide⟩)⟩}, {⟨⟨21,by decide⟩,(⟨8,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨16,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨11,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨13,by decide⟩,(⟨0,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨0,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨0,by decide⟩,⟨8,by decide⟩)⟩}, {⟨⟨21,by decide⟩,(⟨9,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨15,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨12,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨12,by decide⟩,(⟨0,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨0,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨0,by decide⟩,⟨9,by decide⟩)⟩}, {⟨⟨21,by decide⟩,(⟨10,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨14,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨13,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨11,by decide⟩,(⟨0,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨0,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨0,by decide⟩,⟨10,by decide⟩)⟩}, {⟨⟨20,by decide⟩,(⟨5,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨19,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨15,by decide⟩,(⟨0,by decide⟩,⟨4,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨0,by decide⟩,⟨4,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨0,by decide⟩,⟨5,by decide⟩)⟩}, {⟨⟨20,by decide⟩,(⟨6,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨18,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨14,by decide⟩,(⟨0,by decide⟩,⟨4,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨0,by decide⟩,⟨4,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨0,by decide⟩,⟨6,by decide⟩)⟩}, {⟨⟨20,by decide⟩,(⟨7,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨17,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨11,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨13,by decide⟩,(⟨0,by decide⟩,⟨4,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨0,by decide⟩,⟨4,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨0,by decide⟩,⟨7,by decide⟩)⟩}, {⟨⟨20,by decide⟩,(⟨8,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨16,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨12,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨12,by decide⟩,(⟨0,by decide⟩,⟨4,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨0,by decide⟩,⟨4,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨0,by decide⟩,⟨8,by decide⟩)⟩}, {⟨⟨20,by decide⟩,(⟨9,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨15,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨13,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨11,by decide⟩,(⟨0,by decide⟩,⟨4,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨0,by decide⟩,⟨4,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨0,by decide⟩,⟨9,by decide⟩)⟩}, {⟨⟨19,by decide⟩,(⟨6,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨18,by decide⟩,(⟨5,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨11,by decide⟩,(⟨5,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨13,by decide⟩,(⟨0,by decide⟩,⟨5,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨0,by decide⟩,⟨5,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨0,by decide⟩,⟨6,by decide⟩)⟩}, {⟨⟨19,by decide⟩,(⟨7,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨17,by decide⟩,(⟨5,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨12,by decide⟩,(⟨5,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨12,by decide⟩,(⟨0,by decide⟩,⟨5,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨0,by decide⟩,⟨5,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨0,by decide⟩,⟨7,by decide⟩)⟩}, {⟨⟨19,by decide⟩,(⟨8,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨16,by decide⟩,(⟨5,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨13,by decide⟩,(⟨5,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨11,by decide⟩,(⟨0,by decide⟩,⟨5,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨0,by decide⟩,⟨5,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨0,by decide⟩,⟨8,by decide⟩)⟩}, {⟨⟨19,by decide⟩,(⟨9,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨15,by decide⟩,(⟨5,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨14,by decide⟩,(⟨5,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨0,by decide⟩,⟨5,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨0,by decide⟩,⟨5,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨0,by decide⟩,⟨9,by decide⟩)⟩}, {⟨⟨18,by decide⟩,(⟨7,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨17,by decide⟩,(⟨6,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨13,by decide⟩,(⟨6,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨11,by decide⟩,(⟨0,by decide⟩,⟨6,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨0,by decide⟩,⟨6,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨0,by decide⟩,⟨7,by decide⟩)⟩}, {⟨⟨18,by decide⟩,(⟨8,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨16,by decide⟩,(⟨6,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨14,by decide⟩,(⟨6,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨0,by decide⟩,⟨6,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨0,by decide⟩,⟨6,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨0,by decide⟩,⟨8,by decide⟩)⟩}, {⟨⟨17,by decide⟩,(⟨8,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨16,by decide⟩,(⟨7,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨15,by decide⟩,(⟨7,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨0,by decide⟩,⟨7,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨0,by decide⟩,⟨7,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨0,by decide⟩,⟨8,by decide⟩)⟩}, {⟨⟨21,by decide⟩,(⟨3,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨20,by decide⟩,(⟨2,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨2,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨19,by decide⟩,(⟨1,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨1,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨1,by decide⟩,⟨3,by decide⟩)⟩}, {⟨⟨21,by decide⟩,(⟨4,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨19,by decide⟩,(⟨2,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨2,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨18,by decide⟩,(⟨1,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨1,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨1,by decide⟩,⟨4,by decide⟩)⟩}, {⟨⟨21,by decide⟩,(⟨5,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨18,by decide⟩,(⟨2,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨2,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨17,by decide⟩,(⟨1,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨1,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨1,by decide⟩,⟨5,by decide⟩)⟩}, {⟨⟨21,by decide⟩,(⟨6,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨17,by decide⟩,(⟨2,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨2,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨16,by decide⟩,(⟨1,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨1,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨1,by decide⟩,⟨6,by decide⟩)⟩}, {⟨⟨21,by decide⟩,(⟨7,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨16,by decide⟩,(⟨2,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨2,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨15,by decide⟩,(⟨1,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨1,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨1,by decide⟩,⟨7,by decide⟩)⟩}, {⟨⟨21,by decide⟩,(⟨8,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨15,by decide⟩,(⟨2,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨2,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨14,by decide⟩,(⟨1,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨1,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨1,by decide⟩,⟨8,by decide⟩)⟩}, {⟨⟨21,by decide⟩,(⟨9,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨14,by decide⟩,(⟨2,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨11,by decide⟩,(⟨2,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨13,by decide⟩,(⟨1,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨1,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨1,by decide⟩,⟨9,by decide⟩)⟩}, {⟨⟨21,by decide⟩,(⟨10,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨13,by decide⟩,(⟨2,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨12,by decide⟩,(⟨2,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨12,by decide⟩,(⟨1,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨11,by decide⟩,(⟨1,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨1,by decide⟩,⟨10,by decide⟩)⟩}, {⟨⟨20,by decide⟩,(⟨4,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨19,by decide⟩,(⟨3,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨3,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨17,by decide⟩,(⟨1,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨1,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨1,by decide⟩,⟨4,by decide⟩)⟩}, {⟨⟨20,by decide⟩,(⟨5,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨18,by decide⟩,(⟨3,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨3,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨16,by decide⟩,(⟨1,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨1,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨1,by decide⟩,⟨5,by decide⟩)⟩}, {⟨⟨20,by decide⟩,(⟨6,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨17,by decide⟩,(⟨3,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨3,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨15,by decide⟩,(⟨1,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨1,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨1,by decide⟩,⟨6,by decide⟩)⟩}, {⟨⟨20,by decide⟩,(⟨7,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨16,by decide⟩,(⟨3,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨3,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨14,by decide⟩,(⟨1,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨1,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨1,by decide⟩,⟨7,by decide⟩)⟩}, {⟨⟨20,by decide⟩,(⟨8,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨15,by decide⟩,(⟨3,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨11,by decide⟩,(⟨3,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨13,by decide⟩,(⟨1,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨1,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨1,by decide⟩,⟨8,by decide⟩)⟩}, {⟨⟨20,by decide⟩,(⟨9,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨14,by decide⟩,(⟨3,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨12,by decide⟩,(⟨3,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨12,by decide⟩,(⟨1,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨1,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨1,by decide⟩,⟨9,by decide⟩)⟩}, {⟨⟨19,by decide⟩,(⟨5,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨18,by decide⟩,(⟨4,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨4,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨15,by decide⟩,(⟨1,by decide⟩,⟨4,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨1,by decide⟩,⟨4,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨1,by decide⟩,⟨5,by decide⟩)⟩}, {⟨⟨19,by decide⟩,(⟨6,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨17,by decide⟩,(⟨4,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨4,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨14,by decide⟩,(⟨1,by decide⟩,⟨4,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨1,by decide⟩,⟨4,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨1,by decide⟩,⟨6,by decide⟩)⟩}, {⟨⟨19,by decide⟩,(⟨7,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨16,by decide⟩,(⟨4,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨11,by decide⟩,(⟨4,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨13,by decide⟩,(⟨1,by decide⟩,⟨4,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨1,by decide⟩,⟨4,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨1,by decide⟩,⟨7,by decide⟩)⟩}, {⟨⟨19,by decide⟩,(⟨8,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨15,by decide⟩,(⟨4,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨12,by decide⟩,(⟨4,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨12,by decide⟩,(⟨1,by decide⟩,⟨4,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨1,by decide⟩,⟨4,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨1,by decide⟩,⟨8,by decide⟩)⟩}, {⟨⟨19,by decide⟩,(⟨9,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨14,by decide⟩,(⟨4,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨13,by decide⟩,(⟨4,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨11,by decide⟩,(⟨1,by decide⟩,⟨4,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨1,by decide⟩,⟨4,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨1,by decide⟩,⟨9,by decide⟩)⟩}, {⟨⟨18,by decide⟩,(⟨6,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨17,by decide⟩,(⟨5,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨11,by decide⟩,(⟨5,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨13,by decide⟩,(⟨1,by decide⟩,⟨5,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨1,by decide⟩,⟨5,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨1,by decide⟩,⟨6,by decide⟩)⟩}, {⟨⟨18,by decide⟩,(⟨7,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨16,by decide⟩,(⟨5,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨12,by decide⟩,(⟨5,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨12,by decide⟩,(⟨1,by decide⟩,⟨5,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨1,by decide⟩,⟨5,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨1,by decide⟩,⟨7,by decide⟩)⟩}, {⟨⟨18,by decide⟩,(⟨8,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨15,by decide⟩,(⟨5,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨13,by decide⟩,(⟨5,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨11,by decide⟩,(⟨1,by decide⟩,⟨5,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨1,by decide⟩,⟨5,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨1,by decide⟩,⟨8,by decide⟩)⟩}, {⟨⟨17,by decide⟩,(⟨7,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨16,by decide⟩,(⟨6,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨13,by decide⟩,(⟨6,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨11,by decide⟩,(⟨1,by decide⟩,⟨6,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨1,by decide⟩,⟨6,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨1,by decide⟩,⟨7,by decide⟩)⟩}, {⟨⟨17,by decide⟩,(⟨8,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨15,by decide⟩,(⟨6,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨14,by decide⟩,(⟨6,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨1,by decide⟩,⟨6,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨1,by decide⟩,⟨6,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨1,by decide⟩,⟨8,by decide⟩)⟩}, {⟨⟨19,by decide⟩,(⟨4,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨18,by decide⟩,(⟨3,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨3,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨17,by decide⟩,(⟨2,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨2,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨2,by decide⟩,⟨4,by decide⟩)⟩}, {⟨⟨19,by decide⟩,(⟨5,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨17,by decide⟩,(⟨3,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨3,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨16,by decide⟩,(⟨2,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨2,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨2,by decide⟩,⟨5,by decide⟩)⟩}, {⟨⟨19,by decide⟩,(⟨6,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨16,by decide⟩,(⟨3,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨3,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨15,by decide⟩,(⟨2,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨2,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨2,by decide⟩,⟨6,by decide⟩)⟩}, {⟨⟨19,by decide⟩,(⟨7,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨15,by decide⟩,(⟨3,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨3,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨14,by decide⟩,(⟨2,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨2,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨2,by decide⟩,⟨7,by decide⟩)⟩}, {⟨⟨19,by decide⟩,(⟨8,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨14,by decide⟩,(⟨3,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨11,by decide⟩,(⟨3,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨13,by decide⟩,(⟨2,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨2,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨2,by decide⟩,⟨8,by decide⟩)⟩}, {⟨⟨19,by decide⟩,(⟨9,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨13,by decide⟩,(⟨3,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨12,by decide⟩,(⟨3,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨12,by decide⟩,(⟨2,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨11,by decide⟩,(⟨2,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨2,by decide⟩,⟨9,by decide⟩)⟩}, {⟨⟨18,by decide⟩,(⟨5,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨17,by decide⟩,(⟨4,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨4,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨15,by decide⟩,(⟨2,by decide⟩,⟨4,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨2,by decide⟩,⟨4,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨2,by decide⟩,⟨5,by decide⟩)⟩}, {⟨⟨18,by decide⟩,(⟨6,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨16,by decide⟩,(⟨4,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨4,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨14,by decide⟩,(⟨2,by decide⟩,⟨4,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨2,by decide⟩,⟨4,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨2,by decide⟩,⟨6,by decide⟩)⟩}, {⟨⟨18,by decide⟩,(⟨7,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨15,by decide⟩,(⟨4,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨11,by decide⟩,(⟨4,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨13,by decide⟩,(⟨2,by decide⟩,⟨4,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨2,by decide⟩,⟨4,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨2,by decide⟩,⟨7,by decide⟩)⟩}, {⟨⟨18,by decide⟩,(⟨8,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨14,by decide⟩,(⟨4,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨12,by decide⟩,(⟨4,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨12,by decide⟩,(⟨2,by decide⟩,⟨4,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨2,by decide⟩,⟨4,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨2,by decide⟩,⟨8,by decide⟩)⟩}, {⟨⟨17,by decide⟩,(⟨6,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨16,by decide⟩,(⟨5,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨11,by decide⟩,(⟨5,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨13,by decide⟩,(⟨2,by decide⟩,⟨5,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨2,by decide⟩,⟨5,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨2,by decide⟩,⟨6,by decide⟩)⟩}, {⟨⟨17,by decide⟩,(⟨7,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨15,by decide⟩,(⟨5,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨12,by decide⟩,(⟨5,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨12,by decide⟩,(⟨2,by decide⟩,⟨5,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨2,by decide⟩,⟨5,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨2,by decide⟩,⟨7,by decide⟩)⟩}, {⟨⟨17,by decide⟩,(⟨8,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨14,by decide⟩,(⟨5,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨13,by decide⟩,(⟨5,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨11,by decide⟩,(⟨2,by decide⟩,⟨5,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨2,by decide⟩,⟨5,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨2,by decide⟩,⟨8,by decide⟩)⟩}, {⟨⟨16,by decide⟩,(⟨7,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨15,by decide⟩,(⟨6,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨13,by decide⟩,(⟨6,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨11,by decide⟩,(⟨2,by decide⟩,⟨6,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨2,by decide⟩,⟨6,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨2,by decide⟩,⟨7,by decide⟩)⟩}, {⟨⟨17,by decide⟩,(⟨5,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨16,by decide⟩,(⟨4,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨4,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨15,by decide⟩,(⟨3,by decide⟩,⟨4,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨3,by decide⟩,⟨4,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨3,by decide⟩,⟨5,by decide⟩)⟩}, {⟨⟨17,by decide⟩,(⟨6,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨15,by decide⟩,(⟨4,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨4,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨14,by decide⟩,(⟨3,by decide⟩,⟨4,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨3,by decide⟩,⟨4,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨3,by decide⟩,⟨6,by decide⟩)⟩}, {⟨⟨17,by decide⟩,(⟨7,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨14,by decide⟩,(⟨4,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨11,by decide⟩,(⟨4,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨13,by decide⟩,(⟨3,by decide⟩,⟨4,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨3,by decide⟩,⟨4,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨3,by decide⟩,⟨7,by decide⟩)⟩}, {⟨⟨17,by decide⟩,(⟨8,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨13,by decide⟩,(⟨4,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨12,by decide⟩,(⟨4,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨12,by decide⟩,(⟨3,by decide⟩,⟨4,by decide⟩)⟩,⟨⟨11,by decide⟩,(⟨3,by decide⟩,⟨4,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨3,by decide⟩,⟨8,by decide⟩)⟩}, {⟨⟨16,by decide⟩,(⟨6,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨15,by decide⟩,(⟨5,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨11,by decide⟩,(⟨5,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨13,by decide⟩,(⟨3,by decide⟩,⟨5,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨3,by decide⟩,⟨5,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨3,by decide⟩,⟨6,by decide⟩)⟩}, {⟨⟨16,by decide⟩,(⟨7,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨14,by decide⟩,(⟨5,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨12,by decide⟩,(⟨5,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨12,by decide⟩,(⟨3,by decide⟩,⟨5,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨3,by decide⟩,⟨5,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨3,by decide⟩,⟨7,by decide⟩)⟩}, {⟨⟨15,by decide⟩,(⟨7,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨14,by decide⟩,(⟨6,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨13,by decide⟩,(⟨6,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨11,by decide⟩,(⟨3,by decide⟩,⟨6,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨3,by decide⟩,⟨6,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨3,by decide⟩,⟨7,by decide⟩)⟩}, {⟨⟨15,by decide⟩,(⟨6,by decide⟩,⟨4,by decide⟩)⟩,⟨⟨14,by decide⟩,(⟨5,by decide⟩,⟨4,by decide⟩)⟩,⟨⟨11,by decide⟩,(⟨5,by decide⟩,⟨4,by decide⟩)⟩,⟨⟨13,by decide⟩,(⟨4,by decide⟩,⟨5,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨4,by decide⟩,⟨5,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨4,by decide⟩,⟨6,by decide⟩)⟩}, {⟨⟨15,by decide⟩,(⟨7,by decide⟩,⟨4,by decide⟩)⟩,⟨⟨13,by decide⟩,(⟨5,by decide⟩,⟨4,by decide⟩)⟩,⟨⟨12,by decide⟩,(⟨5,by decide⟩,⟨4,by decide⟩)⟩,⟨⟨12,by decide⟩,(⟨4,by decide⟩,⟨5,by decide⟩)⟩,⟨⟨11,by decide⟩,(⟨4,by decide⟩,⟨5,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨4,by decide⟩,⟨7,by decide⟩)⟩}]
def columns : Matrix (Fin 12) (Fin 84) ℚ := ![![42877225028137500, -42877225028137500, 77179005050647500, -77179005050647500, 102905340067530000, -102905340067530000, 120056230078785000, -120056230078785000, 128631675084412500, -128631675084412500, -34301780022510000, 0, -25726335016882500, 0, -17150890011255000, 0, -8575445005627500, 0, 60028115039392500, -34301780022510000, 77179005050647500, -60028115039392500, 85754450056275000, -77179005050647500, 85754450056275000, -42877225028137500, 0, -25726335016882500, 0, -8575445005627500, 51452670033765000, -25726335016882500, 51452670033765000, -42877225028137500, -25726335016882500, 0, 17150890011255000, 34301780022510000, -34301780022510000, 60028115039392500, -60028115039392500, 77179005050647500, -77179005050647500, 85754450056275000, -85754450056275000, -25726335016882500, 0, -17150890011255000, 0, -8575445005627500, 0, 42877225028137500, -25726335016882500, 51452670033765000, -42877225028137500, 51452670033765000, -25726335016882500, 0, -8575445005627500, 25726335016882500, -17150890011255000, 25726335016882500, -25726335016882500, 42877225028137500, -42877225028137500, 51452670033765000, -51452670033765000, -17150890011255000, 0, -8575445005627500, 0, 25726335016882500, -17150890011255000, 25726335016882500, -8575445005627500, 17150890011255000, -17150890011255000, 25726335016882500, -25726335016882500, -8575445005627500, 0, 8575445005627500, 8575445005627500, -8575445005627500], ![31183436384100000, -31183436384100000, 45438721588260000, -45438721588260000, 49893498214560000, -49893498214560000, 49893498214560000, -49893498214560000, 49002542889300000, -49002542889300000, -14255285204160000, 0, -4454776626300000, 0, 0, 0, 890955325260000, 0, 18710061830460000, -14255285204160000, 18710061830460000, -18710061830460000, 17819106505200000, -18710061830460000, 17819106505200000, -4454776626300000, 0, 890955325260000, 0, 890955325260000, 3563821301040000, -4454776626300000, 3563821301040000, -4454776626300000, 890955325260000, 0, 0, 14255285204160000, -14255285204160000, 18710061830460000, -18710061830460000, 18710061830460000, -18710061830460000, 17819106505200000, -17819106505200000, -4454776626300000, 0, 0, 0, 890955325260000, 0, 4454776626300000, -4454776626300000, 3563821301040000, -4454776626300000, 3563821301040000, 890955325260000, 0, 890955325260000, -890955325260000, 0, 4454776626300000, -4454776626300000, 4454776626300000, -4454776626300000, 3563821301040000, -3563821301040000, 0, 0, 890955325260000, 0, -890955325260000, 0, -890955325260000, 890955325260000, 0, 0, -890955325260000, 890955325260000, 890955325260000, 0, -890955325260000, -890955325260000, 890955325260000], ![43072121505538125, -43072121505538125, 49197439366700625, -45258478981340625, 39102387992167500, -32537454016567500, 25377572899428750, -19469132321388750, 15385098618264375, -13040479341264375, -6125317861162500, -3938960385360000, 6156090989173125, -6564933975600000, 7159881117138750, -5908440578040000, 4084033703124375, -2344619277000000, 7847147642709375, -8751291451402500, 6923953802390625, -6205914148809375, 4668723135326250, -3125670573650625, 2793027713726250, 3468571142911875, -3282466987800000, 3647348362783125, -3001112674560000, 1270490570724375, 137746382523750, -877766841826875, 1544517948723750, -1220667411088125, 36634676203125, -468923855400000, 718039653581250, 10064278246522500, -10064278246522500, 9160134437829375, -7518900943929375, 4954473609710625, -2844316260410625, 1386256147526250, -448408436726250, 904143808693125, -1641233493900000, 2564427334218750, -2110157349300000, 1458060112884375, -937847710800000, -186104155111875, -502627757506875, 231531153603750, 186104155111875, -49823159636250, 740020459303125, -703385783100000, 145073317764375, 432289179196875, -249115798181250, 737089685206875, -737089685206875, 48357772588125, 420566082811875, -706316557196250, 987670870436250, 688731912618750, -468923855400000, 285750474384375, -281354313240000, -36634676203125, 126023286138750, 104042480416875, -183173381015625, -219808057218750, 219808057218750, -130419447283125, 177311832823125, -89388609935625, -46892385540000, 183173381015625, 136280995475625, -136280995475625], ![53986324239973125, -53986324239973125, 48529222872755625, -39338315306915625, 28051415799907500, -18500080486387500, 11407779571938750, -6271684167498750, 3097224825069375, -1745620771269375, 5457101367217500, -9190907565840000, 11286899507008125, -9551335313520000, 7092300914448750, -5136095404440000, 3174459342429375, -1351604053800000, 1637814257454375, -3553592324782500, 2970511945025625, -1772974662834375, 1334306740016250, -1058957640365625, 664940922896250, 1889630965096875, -1892245675320000, 882766397638125, -411917425920000, 316782200109375, 831477850953750, -491364390391875, 200729292513750, -298680360103125, 26750496898125, 141596615160000, -244173708528750, 3733806198622500, -3733806198622500, 1818028131294375, -511477545954375, -183230847174375, 627329321994375, -763897648263750, 686663130903750, 1915778067328125, -1306550585340000, 694708393128750, -444098474820000, 136568326269375, 77234517360000, 2614710223125, 178001426728125, 20515418673750, -105594066703125, -18101840006250, -340113460561875, 263884600980000, -43645547570625, -168347112058125, 102577093368750, -609227481988125, 609227481988125, -428611345036875, 287014729876875, -108208776926250, -59132677353750, -180616136951250, 141596615160000, -178805952950625, 167341454280000, 76228859581875, -51891941351250, -58931545798125, 65770018689375, 39019521791250, -39019521791250, 63356440021875, -108409908481875, -24336918230625, 45053468460000, -65770018689375, -20716550229375, 20716550229375], ![57689357310585000, -57689357310585000, 41006218845091500, -26136643390357500, 14894193957142500, -7103162018452500, 2738204998278750, -854648206161750, 107404250703750, 225669605411250, 16683138465493500, -14869575454734000, 11242449433215000, -7791031938690000, 4364957020173750, -1883556792117000, 747243955458000, -333073856115000, 1813563010759500, -1725708747262500, 1857248784641250, -1398910195683000, 630668105817750, -254149833687750, 271527600093750, -288422650766250, 27997512543000, 191396788332750, -30893806944000, -115851776040000, -78441306693750, -67580202690000, 13274682671250, 165330138723750, 119472144041250, -159296192055000, 164847422990250, -1813563010759500, 1813563010759500, -1725708747262500, 1568826133875000, -1082490032373750, 505644730841250, -160020265655250, 61546256021250, -87854263497000, 156882613387500, -486336101501250, 576845301532500, -345624465186000, 98474009634000, 260425138223250, -140952994182000, -92922778698750, 133470900312750, -49478362683750, 146021509383750, -65166624022500, -19308629340000, 39824048013750, -5551230935250, -69028349890500, 69028349890500, 50443794150750, -138298057647750, 113679555239250, -48995646950250, -119472144041250, 87854263497000, 24618502408500, -64683908289000, -80854885361250, 44651205348750, 24859860275250, -34272817078500, 31617880544250, -31617880544250, -4585799468250, 39824048013750, 36203680012500, -35238248545500, 34272817078500, -965431467000, 965431467000], ![42877225028137500, -42877225028137500, 24501271444650000, -9542600457390000, 2514604174582500, -238944288082500, -384965797466250, 491163258836250, -282561102573750, 17650951683750, 18375953583487500, -14958670987260000, 7027996282807500, -2275659886500000, 623910085548750, -106197461370000, -208602156262500, 264910150890000, 4513392108225000, -2924222954152500, 1075249296371250, -424789845480000, 305317701438750, -82711484336250, -184824427961250, 597360720206250, -166881725010000, 36031281536250, -186720811200000, 213853679077500, -115679377563750, 185845557397500, -28153997313750, -161192575293750, -160609072758750, 157545684450000, -133767956148750, -3417282596227500, 3417282596227500, -1828113442155000, 576500504580000, -92922778698750, 9481916193750, 26403489708750, -80085722928750, -1589169154072500, 1251612937575000, -483577725881250, 83440862505000, -35885405902500, 53682233220000, -430478995196250, 246529821037500, -35156027733750, 1021129436250, -52661103783750, -70166179833750, 2917512675000, 31800888157500, 3063388308750, -23777728301250, 337556216497500, -337556216497500, 153607042338750, -12399428868750, -18817956753750, -1021129436250, 183949174158750, -141207613470000, 31217385622500, 19839086190000, 67248667158750, -37781789141250, -8023159856250, 20714339992500, -42741560688750, 42741560688750, -13274682671250, -11815926333750, -29466878017500, 25090609005000, -20714339992500, 4376269012500, -4376269012500], ![-3118343638410000, 3118343638410000, -3341082469725000, 3950683481745000, -3716221554045000, 2389442880825000, -832684640287500, -45857994682500, 92060786317500, 163088958532500, 222738831315000, -609601012020000, -234461927700000, 1326778673220000, -1556758240537500, 878542634970000, -46202791635000, -255149744850000, 1230925120425000, -1355052023325000, 474785403592500, 400654058805000, -608566621162500, 232737942937500, 185845557397500, 898196061262500, -842683751910000, 261700886947500, 220670049600000, -280664719335000, 456855962062500, -386172586800000, 72062563072500, 174122461012500, 216187689217500, -177915227490000, 127919669377500, 386862180705000, -386862180705000, 262735277805000, -244805836275000, 277561546762500, -223773222172500, 68614593547500, 69304187452500, 124126902900000, -17929441530000, -32755710487500, -53788324590000, 155158628625000, -137918781000000, -55512309352500, 124126902900000, -96198349747500, -12067893337500, 106542258322500, -70683375262500, 97922334510000, -68269796595000, -38272461727500, 49995558112500, -106197461370000, 106197461370000, -37582867822500, -5171954287500, -5171954287500, 31376522677500, -68614593547500, 42754822110000, 10343908575000, -26204568390000, -27238959247500, 8619923812500, 18274238482500, -11723096385000, 25859771437500, -25859771437500, 7240736002500, 7930329907500, 18619035435000, -15171065910000, 11723096385000, -3447969525000, 3447969525000], ![-71721903683430000, 71721903683430000, -40538467299330000, 14278731396930000, -2133603542070000, -337901013450000, -461798051715000, 873715477635000, -241357866750000, -530987306850000, -31183436384100000, 26259735902400000, -12145127854860000, 2471504555520000, 799699065165000, -411917425920000, -632357610885000, 772345173600000, -9190907565840000, 6970415191740000, -2505294656865000, -225267342300000, 759472754040000, -101370304035000, -579258880200000, -2527821391095000, 1802138738400000, -411917425920000, -411917425920000, 448925632155000, -765908963820000, 534205411740000, -45053468460000, -275147968095000, -276757020540000, 205958712960000, -130333248045000, 4923700481700000, -4923700481700000, 2703208107600000, -765908963820000, -162514296945000, 284802282765000, -38617258680000, -193086293400000, 2220492374100000, -1937299143780000, 928423260765000, -122287985820000, -246185024085000, 231703552080000, 725682652695000, -624312348660000, 289629440100000, 8045262225000, -173777664060000, 231703552080000, -212394922740000, 114242723595000, 70798307580000, -75625464915000, -283193230320000, 283193230320000, -181822926285000, 78843569805000, 6436209780000, -57925888020000, -101370304035000, 102979356480000, -85279779585000, 51489678240000, -19308629340000, 27353891565000, -38617258680000, 4827157335000, -1609052445000, 1609052445000, 6436209780000, -12872419560000, -8045262225000, 6436209780000, -4827157335000, 1609052445000, -1609052445000], ![-49893498214560000, 49893498214560000, -39202034311440000, 26447305444560000, -12567159324720000, 1312986795120000, 4048375951620000, -3610713686580000, 234461927700000, 2579081204700000, -10691463903120000, 12754728866880000, -13880146119840000, 11254172529600000, -5361362746740000, -437662265040000, 3376251758880000, -2813543132400000, -937847710800000, 2813543132400000, -4642346168460000, 4376622650400000, -2203942120380000, -422031469860000, 2110157349300000, 390769879500000, 437662265040000, -1484925542100000, 1750649060160000, -1125417252960000, 422031469860000, -125046361440000, -390769879500000, 703385783100000, 265723518060000, -187569542160000, 109415566260000, -2063264963760000, 2063264963760000, -187569542160000, -1250463614400000, 1422402361380000, -734647373460000, -140677156620000, 703385783100000, -1875695421600000, 1438033156560000, -171938746980000, -687754987920000, 875324530080000, -562708626480000, -828432144540000, 625231807200000, -140677156620000, -234461927700000, 422031469860000, -296985108420000, 250092722880000, -125046361440000, -78153975900000, 78153975900000, 437662265040000, -437662265040000, 234461927700000, -46892385540000, -78153975900000, 140677156620000, 203200337340000, -187569542160000, 125046361440000, -62523180720000, 46892385540000, -46892385540000, 46892385540000, 0, -15630795180000, 15630795180000, -15630795180000, 15630795180000, 0, 0, 0, 0, 0], ![536355105806520000, -536355105806520000, 314329038751728000, -117606102934320000, 5345731951560000, 37420123660920000, -37420123660920000, 17462724375096000, 5345731951560000, -19601017155720000, 222026067054792000, -196722935817408000, 112260370982760000, -42765855612480000, 0, 19957399285824000, -22808456326656000, 14255285204160000, 59159433597264000, -51675408865080000, 32074391709360000, -14968049464368000, 2138292780624000, 6414878341872000, -10691463903120000, 12473374553640000, -11404228163328000, 8553171122496000, -5702114081664000, 2851057040832000, 1781910650520000, -1781910650520000, 1781910650520000, -1781910650520000, 0, 0, 0, -25303131237384000, 25303131237384000, -17819106505200000, 10691463903120000, -4989349821456000, 712764260208000, 2138292780624000, -3563821301040000, -7484024732184000, 7127642602080000, -5702114081664000, 4276585561248000, -2851057040832000, 1425528520416000, -1069146390312000, 1069146390312000, -1069146390312000, 1069146390312000, -1069146390312000, 0, 0, 0, 0, 0, 356382130104000, -356382130104000, 356382130104000, -356382130104000, 356382130104000, -356382130104000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![3243077383946400000, -3243077383946400000, 2519621659835280000, -1821112684831440000, 1222390706256720000, -723455724111120000, 324307738394640000, -24946749107280000, -174627243750960000, 274414240180080000, 723455724111120000, -698508975003840000, 598721978574720000, -498934982145600000, 399147985716480000, -299360989287360000, 199573992858240000, -99786996429120000, 74840247321840000, -74840247321840000, 74840247321840000, -74840247321840000, 74840247321840000, -74840247321840000, 74840247321840000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -24946749107280000, 24946749107280000, -24946749107280000, 24946749107280000, -24946749107280000, 24946749107280000, -24946749107280000, 24946749107280000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![12623055048283680000, -12623055048283680000, 12623055048283680000, -12623055048283680000, 12623055048283680000, -12623055048283680000, 12623055048283680000, -12623055048283680000, 12623055048283680000, -12623055048283680000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]
def Y : Matrix (Fin 12) (Fin 12) ℚ := ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]
def Z : Matrix (Fin 12) (Fin 12) ℚ := ![![2248001455555215360000, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2195313921440640000, 252461100965673600000], ![0, 14597412049059840000, 0, 0, 0, 0, 0, 0, 0, -57021140816640000, 0, 100984440386269440000], ![0, 0, 768284844687360000, 0, 0, 0, 0, 0, -4501669011840000, -114042281633280000, 1746272437509600000, 37869165144851040000], ![0, 0, 0, 105450861035520000, 0, 0, 0, -823834851840000, -24509086842240000, 0, 1746272437509600000, 12623055048283680000], ![0, 0, 0, 0, 31635258310656000, 0, -308938069440000, -8341327874880000, -26259735902400000, 119744395714944000, 1010343338844840000, 3155763762070920000], ![0, 0, 0, 0, 0, 18896146093440000, -4854741091200000, -16991593819200000, 0, 117606102934320000, 274414240180080000, 0], ![0, 0, 0, 0, -308938069440000, -4854741091200000, 8396495387280000, -11044535982480000, 13411222264440000, 0, -202692336496650000, -788940940517730000], ![0, 0, 0, -823834851840000, -8341327874880000, -16991593819200000, -11044535982480000, 52725430517760000, -31292851950360000, -162153869197320000, -420976391185350000, -788940940517730000], ![0, 0, -4501669011840000, -24509086842240000, -26259735902400000, 0, 13411222264440000, -31292851950360000, 111009907368360000, -302924810588400000, -463853616213487500, -591705705388297500], ![0, -57021140816640000, -114042281633280000, 0, 119744395714944000, 117606102934320000, 0, -162153869197320000, -302924810588400000, 2530981340232345000, -414739703908530000, -394470470258865000], ![-2195313921440640000, 0, 1746272437509600000, 1746272437509600000, 1010343338844840000, 274414240180080000, -202692336496650000, -420976391185350000, -463853616213487500, -414739703908530000, 101850365435360416875, -246544043911790625], ![252461100965673600000, 100984440386269440000, 37869165144851040000, 12623055048283680000, 3155763762070920000, 0, -788940940517730000, -788940940517730000, -591705705388297500, -394470470258865000, -246544043911790625, 25851868812458629565625]]
def W : Matrix (Fin 12) (Fin 12) ℚ := ![![(400001/100000), 0, 0, 0, 0, 0, 0, 0, 0, 0, (-11/102400000), (1/20480000)], ![0, (1/200000), 0, 0, 0, 0, 0, 0, 0, (-1/10240000), 0, (1/51200000)], ![0, 0, (1/200000), 0, 0, 0, 0, 0, (-9/102400000), (-1/5120000), (7/81920000), (3/409600000)], ![0, 0, 0, (1/200000), 0, 0, 0, (-1/12800000), (-49/102400000), 0, (7/81920000), (1/409600000)], ![0, 0, 0, 0, (1/200000), 0, (-7/102400000), (-81/102400000), (-21/40960000), (21/102400000), (81/1638400000), (1/1638400000)], ![0, 0, 0, 0, 0, (253/51200000), (-11/10240000), (-33/20480000), 0, (33/163840000), (11/819200000), 0], ![0, 0, 0, 0, (-1/20480000), (-13/10240000), (761/409600000), (-429/409600000), (429/1638400000), 0, (-13/1310720000), (-1/6553600000)], ![0, 0, 0, (-1/25600000), (-27/20480000), (-91/20480000), (-1001/409600000), (1/200000), (-1001/1638400000), (-91/327680000), (-27/1310720000), (-1/6553600000)], ![0, 0, (-3/102400000), (-119/102400000), (-17/4096000), 0, (2431/819200000), (-2431/819200000), (3551/1638400000), (-17/32768000), (-119/5242880000), (-3/26214400000)], ![0, (-1/51200000), (-19/25600000), 0, (969/51200000), (12597/409600000), 0, (-12597/819200000), (-969/163840000), (11363/2621440000), (-133/6553600000), (-1/13107200000)], ![(-400001/102400000), 0, (931/81920000), (6783/81920000), (26163/163840000), (29393/409600000), (-29393/655360000), (-26163/655360000), (-47481/5242880000), (-931/1310720000), (522587/104857600000), (-1/20971520000)], ![(9200023/20480000), (1771/51200000), (100947/409600000), (245157/409600000), (81719/163840000), 0, (-572033/3276800000), (-245157/3276800000), (-302841/26214400000), (-1771/2621440000), (-253/20971520000), (104857/20971520000)]]
def M : Matrix (Fin 12) (Fin 12) ℚ := ![![(719362265183875514031831/80), (78894094051773/16), (106335518069781/64), (3430178002251/8), (58313026038267/1280), (-37731958024761/1280), (-17150890011255/1024), (3430178002251/512), (85754450056275/4096), (517956878339901/20480), (-719363161448225366191119/81920), (4136338189510533687437757/4096)], ![(78894094051773/16), (374824905336882/5), (240246103456359/320), (78894094051773/320), (12785208917481/256), (-1470076286679/128), (-78894094051773/5120), (2182840546887/5120), (369167339021481/20480), (-2764678922048043/5120), (584689432201875/16384), (82729372645911840849/81920)], ![(106335518069781/64), (240246103456359/320), (5492061985256847/1280), (39012120150003/160), (452438837263413/5120), (490025428893/1024), (-497192930022789/20480), (-75053607676047/10240), (-1398356727614847/81920), (-88166221573987557/81920), (1150442722659505275/65536), (31031177331101718771/81920)], ![(3430178002251/8), (78894094051773/320), (39012120150003/160), (920425304681883/1280), (68643142735167/640), (25370573521293/1024), (-63489669564321/2560), (-638207160143553/20480), (-2194444067688873/10240), (1986073063303329/16384), (144905375030182767/8192), (41469181550527493763/327680)], ![(58313026038267/1280), (12785208917481/256), (452438837263413/5120), (68643142735167/640), (26080429212328491/102400), (210770101581039/4096), (-881497820690487/81920), (-4962826522763109/40960), (-81852236888843421/327680), (2261975688902022093/1638400), (13875949703845690461/1310720), (10631847008510981253/327680)], ![(-37731958024761/1280), (-1470076286679/128), (490025428893/1024), (25370573521293/1024), (210770101581039/4096), (78510149383743/512), (-293834721651471/16384), (-3200929542391581/16384), (-2046423563493309/65536), (220632479282786571/163840), (4634894248599575961/1310720), (533718546260244345/262144)], ![(-17150890011255/1024), (-78894094051773/5120), (-497192930022789/20480), (-63489669564321/2560), (-881497820690487/81920), (-293834721651471/16384), (12775666454942391/327680), (-1889462336400639/32768), (24309099414849249/262144), (-79248649723460217/1310720), (-1536133808238790761/1048576), (-6410381823988711569/1310720)], ![(3430178002251/512), (2182840546887/5120), (-75053607676047/10240), (-638207160143553/20480), (-4962826522763109/40960), (-3200929542391581/16384), (-1889462336400639/32768), (147485437848820071/327680), (-83698843400613441/655360), (-2621966009882260041/1310720), (-3108243635199553851/524288), (-10631215855758567069/1048576)], ![(85754450056275/4096), (369167339021481/20480), (-1398356727614847/81920), (-2194444067688873/10240), (-81852236888843421/327680), (-2046423563493309/65536), (24309099414849249/262144), (-83698843400613441/655360), (3557893010133621159/5242880), (-2068428028768308207/1048576), (-36607721238369964683/4194304), (-34505673233141801691/1048576)], ![(517956878339901/20480), (-2764678922048043/5120), (-88166221573987557/81920), (1986073063303329/16384), (2261975688902022093/1638400), (220632479282786571/163840), (-79248649723460217/1310720), (-2621966009882260041/1310720), (-2068428028768308207/1048576), (69577338265481805759/3276800), (663057165751036947891/20971520), (872434639146815417673/20971520)], ![(-719363161448225366191119/81920), (584689432201875/16384), (1150442722659505275/65536), (144905375030182767/8192), (13875949703845690461/1310720), (4634894248599575961/1310720), (-1536133808238790761/1048576), (-3108243635199553851/524288), (-36607721238369964683/4194304), (663057165751036947891/20971520), (793472230046333663913087/83886080), (-4127736559884387492195153/4194304)], ![(4136338189510533687437757/4096), (82729372645911840849/81920), (31031177331101718771/81920), (41469181550527493763/327680), (10631847008510981253/327680), (533718546260244345/262144), (-6410381823988711569/1310720), (-10631215855758567069/1048576), (-34505673233141801691/1048576), (872434639146815417673/20971520), (-4127736559884387492195153/4194304), (1905253556423838329417099391/16777216)]]
def L : Matrix (Fin 12) (Fin 12) ℚ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![(115/209715724581), 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![(155/838862898324), (25704475029382/2566615427724929), 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![(10/209715724581), (4823461660763/1466637387271388), (42273449148319317047/750191596060481726171), 1, 0, 0, 0, 0, 0, 0, 0, 0], ![(1/197379505488), (244271156350/366659346817847), (30779617648760626891/1500383192120963452342), (30477199392796926300916086/210265651248130218677263415), 1, 0, 0, 0, 0, 0, 0, 0], ![(-1/305041053936), (-6291471728575/41065846843598864), (103961918291566170/750191596060481726171), (1344390397902047182604553/38230118408750948850411530), (3335650689270226358315406623215/16590794336554066450644608161726), 1, 0, 0, 0, 0, 0, 0], ![(-25/13421806373184), (-9884142751/48086471713816), (-67601131021086359207/12003065536967707618736), (-13959002725254002801868729/420531302496260437354526830), (-956895589116657171521172971595/33181588673108132901289216323452), (-34077466479713603480659996756084849/309447980022555881300966047939372551), 1, 0, 0, 0, 0, 0], ![(5/6710903186592), (133455459947/23466198196342208), (-20551947050717837657/12003065536967707618736), (-146809989156775311435372987/3364250419970083498836214640), (-4641851609721589716495861958185/9480453906602323686082633235272), (-4441488196267679852006070698900689583/3713375760270670575611592575272470612), (-5280432445724671717665493840992066646685/2359065529261681880350961572828935619119), 1, 0, 0, 0, 0], ![(125/53687225492736), (617157034267/2566615427724929), (-48342083157145507629/12003065536967707618736), (-23153683272129950497860009/76460236817501897700823060), (-60918755999324663108684057350715/66363177346216265802578432646904), (131395803727585505079910898628691529/928343940067667643902898143818117653), (5318293573619528711290060370797803607667/2359065529261681880350961572828935619119), (-13027197312078228082098695632569243402590420/2165384596732381358615964581579253982085263), 1, 0, 0, 0], ![(151/53687225492736), (-4732788212202079/657053549497581824), (-1500455164382774234879/6001532768483853809368), (4376479710843642526484299167/16821252099850417494181073200), (767391364143321956604257826343773/132726354692432531605156865293808), (92158418805367722954035822815113831197/12377919200902235252038641917574902040), (10475252818259790164102980806742481468056/3931775882102803133918269288048226031865), (290647770973386155406544308225163462383331971/10826922983661906793079822907896269910426315), (-76/5), 1, 0, 0], ![(-69905328623/71582967323648), (25356541364445/46932396392684416), (787161044680496502221975/192049048591483321899776), (15945561689262782529370349169/672850083994016699767242928), (1243477381072346524209861164239165/37921815626409294744330532941088), (23864947565445718263864628801716377803/2475583840180447050407728383514980408), (-75720259252818328140805876227765084142127/6290841411364485014269230860877161650984), (-234403275407970870776645169080095257098760459/2165384596732381358615964581579253982085263), (931/4), 0, 1, 0], ![(182707109395/1626885620992), (5055171113380675419/375459171141475328), (16523048659928326437893279/192049048591483321899776), (711243624735671388174656954937/4893455156320121452852675840), (2983098331522191665972814029830865/75843631252818589488661065882176), (-21057369184542869807596952885046033797/900212305520162563784628503096356512), (121110569964989727799501535376726321606191/6290841411364485014269230860877161650984), (-8060994593626767754612029529730338302597950325/17323076773859050868927716652634031856682104), (-33649/4), 0, 0, 1]]
def diag : Fin 12 → ℚ := ![(719362265183875514031831/80), (2241901650221566802946477/29905985680), (251273382509543244726680285481/58665495490855520), (67665692048064246008207072762959935/96024524295741660949888), (728057950683394731739150325146150246911/3058409472700075908032922400), (108338208476274428350963672152933245890750071/758436312528185894886610658821760), (108453147364963664982597490767469840705457591313/3000707685067208545948761676987855040), (6271591283527639024356191326842301046070501531512463/1006534625818317602283076937740345864157440), (43644256453302925372827507467823711516761413624303125/34646153547718101737855433305268063713364208), 0, 0, 0]

def keyIndexTable : Fin 24 → Fin 13 → Fin 13 → Fin 84 := ![![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]], ![![0, 0, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]], ![![0, 0, 0, 10, 11, 12, 13, 14, 15, 16, 17, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]], ![![0, 1, 10, 0, 18, 19, 20, 21, 22, 23, 24, 0, 0], ![0, 0, 0, 37, 38, 39, 40, 41, 42, 43, 44, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]], ![![0, 2, 11, 18, 0, 25, 26, 27, 28, 29, 0, 0, 0], ![1, 0, 37, 0, 45, 46, 47, 48, 49, 50, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]], ![![0, 3, 12, 19, 25, 0, 30, 31, 32, 33, 0, 0, 0], ![2, 0, 38, 45, 0, 51, 52, 53, 54, 55, 0, 0, 0], ![10, 37, 0, 0, 61, 62, 63, 64, 65, 66, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]], ![![0, 4, 13, 20, 26, 30, 0, 34, 35, 0, 0, 0, 0], ![3, 0, 39, 46, 51, 0, 56, 57, 58, 0, 0, 0, 0], ![11, 38, 0, 61, 0, 67, 68, 69, 70, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]], ![![0, 5, 14, 21, 27, 31, 34, 0, 36, 0, 0, 0, 0], ![4, 0, 40, 47, 52, 56, 0, 59, 60, 0, 0, 0, 0], ![12, 39, 0, 62, 67, 0, 71, 72, 73, 0, 0, 0, 0], ![18, 45, 61, 0, 0, 75, 76, 77, 78, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]], ![![0, 6, 15, 22, 28, 32, 35, 36, 0, 0, 0, 0, 0], ![5, 0, 41, 48, 53, 57, 59, 0, 0, 0, 0, 0, 0], ![13, 40, 0, 63, 68, 71, 0, 74, 0, 0, 0, 0, 0], ![19, 46, 62, 0, 75, 0, 79, 80, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]], ![![0, 7, 16, 23, 29, 33, 0, 36, 0, 0, 0, 0, 0], ![6, 0, 42, 49, 54, 58, 60, 0, 0, 0, 0, 0, 0], ![14, 41, 0, 64, 69, 72, 74, 0, 0, 0, 0, 0, 0], ![20, 47, 63, 0, 76, 79, 0, 81, 0, 0, 0, 0, 0], ![25, 51, 67, 75, 0, 0, 82, 83, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]], ![![0, 8, 17, 24, 0, 33, 35, 0, 0, 0, 0, 0, 0], ![7, 0, 43, 50, 55, 0, 60, 0, 0, 0, 0, 0, 0], ![15, 42, 0, 65, 70, 73, 0, 0, 0, 0, 0, 0, 0], ![21, 48, 64, 0, 77, 80, 81, 0, 0, 0, 0, 0, 0], ![26, 52, 68, 76, 0, 82, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]], ![![0, 9, 0, 24, 29, 32, 34, 0, 0, 0, 0, 0, 0], ![8, 0, 44, 0, 55, 58, 59, 0, 0, 0, 0, 0, 0], ![16, 43, 0, 66, 0, 73, 74, 0, 0, 0, 0, 0, 0], ![22, 49, 65, 0, 78, 0, 81, 0, 0, 0, 0, 0, 0], ![27, 53, 69, 77, 0, 83, 0, 0, 0, 0, 0, 0, 0], ![30, 56, 71, 79, 82, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]], ![![0, 9, 17, 23, 28, 31, 0, 0, 0, 0, 0, 0, 0], ![9, 0, 44, 50, 54, 57, 0, 0, 0, 0, 0, 0, 0], ![17, 44, 0, 66, 70, 72, 0, 0, 0, 0, 0, 0, 0], ![23, 50, 66, 0, 78, 80, 0, 0, 0, 0, 0, 0, 0], ![28, 54, 70, 78, 0, 83, 0, 0, 0, 0, 0, 0, 0], ![31, 57, 72, 80, 83, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]], ![![0, 8, 16, 22, 27, 30, 0, 0, 0, 0, 0, 0, 0], ![9, 0, 43, 49, 53, 56, 0, 0, 0, 0, 0, 0, 0], ![0, 44, 0, 65, 69, 71, 0, 0, 0, 0, 0, 0, 0], ![24, 0, 66, 0, 77, 79, 0, 0, 0, 0, 0, 0, 0], ![29, 55, 0, 78, 0, 82, 0, 0, 0, 0, 0, 0, 0], ![32, 58, 73, 0, 83, 0, 0, 0, 0, 0, 0, 0, 0], ![34, 59, 74, 81, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]], ![![0, 7, 15, 21, 26, 0, 0, 0, 0, 0, 0, 0, 0], ![8, 0, 42, 48, 52, 0, 0, 0, 0, 0, 0, 0, 0], ![17, 43, 0, 64, 68, 0, 0, 0, 0, 0, 0, 0, 0], ![24, 50, 65, 0, 76, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 55, 70, 77, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![33, 0, 73, 80, 82, 0, 0, 0, 0, 0, 0, 0, 0], ![35, 60, 0, 81, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]], ![![0, 6, 14, 20, 25, 0, 0, 0, 0, 0, 0, 0, 0], ![7, 0, 41, 47, 51, 0, 0, 0, 0, 0, 0, 0, 0], ![16, 42, 0, 63, 67, 0, 0, 0, 0, 0, 0, 0, 0], ![23, 49, 64, 0, 75, 0, 0, 0, 0, 0, 0, 0, 0], ![29, 54, 69, 76, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![33, 58, 72, 79, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 60, 74, 0, 82, 0, 0, 0, 0, 0, 0, 0, 0], ![36, 0, 0, 81, 83, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]], ![![0, 5, 13, 19, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![6, 0, 40, 46, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![15, 41, 0, 62, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![22, 48, 63, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![28, 53, 68, 75, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![32, 57, 71, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![35, 59, 0, 79, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![36, 0, 74, 80, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]], ![![0, 4, 12, 18, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![5, 0, 39, 45, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![14, 40, 0, 61, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![21, 47, 62, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![27, 52, 67, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![31, 56, 0, 75, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![34, 0, 71, 76, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 59, 72, 77, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![36, 60, 73, 78, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]], ![![0, 3, 11, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![4, 0, 38, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![13, 39, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![20, 46, 61, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![26, 51, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![30, 0, 67, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 56, 68, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![34, 57, 69, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![35, 58, 70, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]], ![![0, 2, 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![3, 0, 37, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![12, 38, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![19, 45, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![25, 0, 61, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 51, 62, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![30, 52, 63, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![31, 53, 64, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![32, 54, 65, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![33, 55, 66, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![11, 37, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![18, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 45, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![25, 46, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![26, 47, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![27, 48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![28, 49, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![29, 50, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 37, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![18, 38, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![19, 39, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![20, 40, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![21, 41, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![22, 42, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![23, 43, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![24, 44, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![11, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![13, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![14, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![15, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![17, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]]
def keyIndex (n : Fin 24) (j : Fin ((n.val+1)/2)) (x : Fin ((23-n.val+2)/2)) : Fin 84 :=
  keyIndexTable n ⟨j.val,by have := j.isLt; have := n.isLt; omega⟩ ⟨x.val,by have := x.isLt; omega⟩
def representatives : Fin 84 → FourTerm 23 := ![⟨⟨23,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨23,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨23,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨23,by decide⟩,(⟨5,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨23,by decide⟩,(⟨6,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨23,by decide⟩,(⟨7,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨23,by decide⟩,(⟨8,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨23,by decide⟩,(⟨9,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨23,by decide⟩,(⟨10,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨23,by decide⟩,(⟨11,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨22,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨22,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨22,by decide⟩,(⟨5,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨22,by decide⟩,(⟨6,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨22,by decide⟩,(⟨7,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨22,by decide⟩,(⟨8,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨22,by decide⟩,(⟨9,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨22,by decide⟩,(⟨10,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨21,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨21,by decide⟩,(⟨5,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨21,by decide⟩,(⟨6,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨21,by decide⟩,(⟨7,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨21,by decide⟩,(⟨8,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨21,by decide⟩,(⟨9,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨21,by decide⟩,(⟨10,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨20,by decide⟩,(⟨5,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨20,by decide⟩,(⟨6,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨20,by decide⟩,(⟨7,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨20,by decide⟩,(⟨8,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨20,by decide⟩,(⟨9,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨19,by decide⟩,(⟨6,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨19,by decide⟩,(⟨7,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨19,by decide⟩,(⟨8,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨19,by decide⟩,(⟨9,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨18,by decide⟩,(⟨7,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨18,by decide⟩,(⟨8,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨17,by decide⟩,(⟨8,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨21,by decide⟩,(⟨3,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨21,by decide⟩,(⟨4,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨21,by decide⟩,(⟨5,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨21,by decide⟩,(⟨6,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨21,by decide⟩,(⟨7,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨21,by decide⟩,(⟨8,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨21,by decide⟩,(⟨9,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨21,by decide⟩,(⟨10,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨20,by decide⟩,(⟨4,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨20,by decide⟩,(⟨5,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨20,by decide⟩,(⟨6,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨20,by decide⟩,(⟨7,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨20,by decide⟩,(⟨8,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨20,by decide⟩,(⟨9,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨19,by decide⟩,(⟨5,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨19,by decide⟩,(⟨6,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨19,by decide⟩,(⟨7,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨19,by decide⟩,(⟨8,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨19,by decide⟩,(⟨9,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨18,by decide⟩,(⟨6,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨18,by decide⟩,(⟨7,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨18,by decide⟩,(⟨8,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨17,by decide⟩,(⟨7,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨17,by decide⟩,(⟨8,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨19,by decide⟩,(⟨4,by decide⟩,⟨2,by decide⟩)⟩, ⟨⟨19,by decide⟩,(⟨5,by decide⟩,⟨2,by decide⟩)⟩, ⟨⟨19,by decide⟩,(⟨6,by decide⟩,⟨2,by decide⟩)⟩, ⟨⟨19,by decide⟩,(⟨7,by decide⟩,⟨2,by decide⟩)⟩, ⟨⟨19,by decide⟩,(⟨8,by decide⟩,⟨2,by decide⟩)⟩, ⟨⟨19,by decide⟩,(⟨9,by decide⟩,⟨2,by decide⟩)⟩, ⟨⟨18,by decide⟩,(⟨5,by decide⟩,⟨2,by decide⟩)⟩, ⟨⟨18,by decide⟩,(⟨6,by decide⟩,⟨2,by decide⟩)⟩, ⟨⟨18,by decide⟩,(⟨7,by decide⟩,⟨2,by decide⟩)⟩, ⟨⟨18,by decide⟩,(⟨8,by decide⟩,⟨2,by decide⟩)⟩, ⟨⟨17,by decide⟩,(⟨6,by decide⟩,⟨2,by decide⟩)⟩, ⟨⟨17,by decide⟩,(⟨7,by decide⟩,⟨2,by decide⟩)⟩, ⟨⟨17,by decide⟩,(⟨8,by decide⟩,⟨2,by decide⟩)⟩, ⟨⟨16,by decide⟩,(⟨7,by decide⟩,⟨2,by decide⟩)⟩, ⟨⟨17,by decide⟩,(⟨5,by decide⟩,⟨3,by decide⟩)⟩, ⟨⟨17,by decide⟩,(⟨6,by decide⟩,⟨3,by decide⟩)⟩, ⟨⟨17,by decide⟩,(⟨7,by decide⟩,⟨3,by decide⟩)⟩, ⟨⟨17,by decide⟩,(⟨8,by decide⟩,⟨3,by decide⟩)⟩, ⟨⟨16,by decide⟩,(⟨6,by decide⟩,⟨3,by decide⟩)⟩, ⟨⟨16,by decide⟩,(⟨7,by decide⟩,⟨3,by decide⟩)⟩, ⟨⟨15,by decide⟩,(⟨7,by decide⟩,⟨3,by decide⟩)⟩, ⟨⟨15,by decide⟩,(⟨6,by decide⟩,⟨4,by decide⟩)⟩, ⟨⟨15,by decide⟩,(⟨7,by decide⟩,⟨4,by decide⟩)⟩]
lemma cover_0 : ∀ j : Fin 0, ∀ x : Fin 12,
  (fourTermLabels (by omega : 23 ≤ 23) ⟨0,j,x⟩).Nodup →
    (fourTermLabels (by omega : 23 ≤ 23) ⟨0,j,x⟩).toFinset=keys (keyIndex 0 j x) := by decide +kernel
lemma cover_1 : ∀ j : Fin 1, ∀ x : Fin 12,
  (fourTermLabels (by omega : 23 ≤ 23) ⟨1,j,x⟩).Nodup →
    (fourTermLabels (by omega : 23 ≤ 23) ⟨1,j,x⟩).toFinset=keys (keyIndex 1 j x) := by decide +kernel
lemma cover_2 : ∀ j : Fin 1, ∀ x : Fin 11,
  (fourTermLabels (by omega : 23 ≤ 23) ⟨2,j,x⟩).Nodup →
    (fourTermLabels (by omega : 23 ≤ 23) ⟨2,j,x⟩).toFinset=keys (keyIndex 2 j x) := by decide +kernel
lemma cover_3 : ∀ j : Fin 2, ∀ x : Fin 11,
  (fourTermLabels (by omega : 23 ≤ 23) ⟨3,j,x⟩).Nodup →
    (fourTermLabels (by omega : 23 ≤ 23) ⟨3,j,x⟩).toFinset=keys (keyIndex 3 j x) := by decide +kernel
lemma cover_4 : ∀ j : Fin 2, ∀ x : Fin 10,
  (fourTermLabels (by omega : 23 ≤ 23) ⟨4,j,x⟩).Nodup →
    (fourTermLabels (by omega : 23 ≤ 23) ⟨4,j,x⟩).toFinset=keys (keyIndex 4 j x) := by decide +kernel
lemma cover_5 : ∀ j : Fin 3, ∀ x : Fin 10,
  (fourTermLabels (by omega : 23 ≤ 23) ⟨5,j,x⟩).Nodup →
    (fourTermLabels (by omega : 23 ≤ 23) ⟨5,j,x⟩).toFinset=keys (keyIndex 5 j x) := by decide +kernel
lemma cover_6 : ∀ j : Fin 3, ∀ x : Fin 9,
  (fourTermLabels (by omega : 23 ≤ 23) ⟨6,j,x⟩).Nodup →
    (fourTermLabels (by omega : 23 ≤ 23) ⟨6,j,x⟩).toFinset=keys (keyIndex 6 j x) := by decide +kernel
lemma cover_7 : ∀ j : Fin 4, ∀ x : Fin 9,
  (fourTermLabels (by omega : 23 ≤ 23) ⟨7,j,x⟩).Nodup →
    (fourTermLabels (by omega : 23 ≤ 23) ⟨7,j,x⟩).toFinset=keys (keyIndex 7 j x) := by decide +kernel
lemma cover_8 : ∀ j : Fin 4, ∀ x : Fin 8,
  (fourTermLabels (by omega : 23 ≤ 23) ⟨8,j,x⟩).Nodup →
    (fourTermLabels (by omega : 23 ≤ 23) ⟨8,j,x⟩).toFinset=keys (keyIndex 8 j x) := by decide +kernel
lemma cover_9 : ∀ j : Fin 5, ∀ x : Fin 8,
  (fourTermLabels (by omega : 23 ≤ 23) ⟨9,j,x⟩).Nodup →
    (fourTermLabels (by omega : 23 ≤ 23) ⟨9,j,x⟩).toFinset=keys (keyIndex 9 j x) := by decide +kernel
lemma cover_10 : ∀ j : Fin 5, ∀ x : Fin 7,
  (fourTermLabels (by omega : 23 ≤ 23) ⟨10,j,x⟩).Nodup →
    (fourTermLabels (by omega : 23 ≤ 23) ⟨10,j,x⟩).toFinset=keys (keyIndex 10 j x) := by decide +kernel
lemma cover_11 : ∀ j : Fin 6, ∀ x : Fin 7,
  (fourTermLabels (by omega : 23 ≤ 23) ⟨11,j,x⟩).Nodup →
    (fourTermLabels (by omega : 23 ≤ 23) ⟨11,j,x⟩).toFinset=keys (keyIndex 11 j x) := by decide +kernel
lemma cover_12 : ∀ j : Fin 6, ∀ x : Fin 6,
  (fourTermLabels (by omega : 23 ≤ 23) ⟨12,j,x⟩).Nodup →
    (fourTermLabels (by omega : 23 ≤ 23) ⟨12,j,x⟩).toFinset=keys (keyIndex 12 j x) := by decide +kernel
lemma cover_13 : ∀ j : Fin 7, ∀ x : Fin 6,
  (fourTermLabels (by omega : 23 ≤ 23) ⟨13,j,x⟩).Nodup →
    (fourTermLabels (by omega : 23 ≤ 23) ⟨13,j,x⟩).toFinset=keys (keyIndex 13 j x) := by decide +kernel
lemma cover_14 : ∀ j : Fin 7, ∀ x : Fin 5,
  (fourTermLabels (by omega : 23 ≤ 23) ⟨14,j,x⟩).Nodup →
    (fourTermLabels (by omega : 23 ≤ 23) ⟨14,j,x⟩).toFinset=keys (keyIndex 14 j x) := by decide +kernel
lemma cover_15 : ∀ j : Fin 8, ∀ x : Fin 5,
  (fourTermLabels (by omega : 23 ≤ 23) ⟨15,j,x⟩).Nodup →
    (fourTermLabels (by omega : 23 ≤ 23) ⟨15,j,x⟩).toFinset=keys (keyIndex 15 j x) := by decide +kernel
lemma cover_16 : ∀ j : Fin 8, ∀ x : Fin 4,
  (fourTermLabels (by omega : 23 ≤ 23) ⟨16,j,x⟩).Nodup →
    (fourTermLabels (by omega : 23 ≤ 23) ⟨16,j,x⟩).toFinset=keys (keyIndex 16 j x) := by decide +kernel
lemma cover_17 : ∀ j : Fin 9, ∀ x : Fin 4,
  (fourTermLabels (by omega : 23 ≤ 23) ⟨17,j,x⟩).Nodup →
    (fourTermLabels (by omega : 23 ≤ 23) ⟨17,j,x⟩).toFinset=keys (keyIndex 17 j x) := by decide +kernel
lemma cover_18 : ∀ j : Fin 9, ∀ x : Fin 3,
  (fourTermLabels (by omega : 23 ≤ 23) ⟨18,j,x⟩).Nodup →
    (fourTermLabels (by omega : 23 ≤ 23) ⟨18,j,x⟩).toFinset=keys (keyIndex 18 j x) := by decide +kernel
lemma cover_19 : ∀ j : Fin 10, ∀ x : Fin 3,
  (fourTermLabels (by omega : 23 ≤ 23) ⟨19,j,x⟩).Nodup →
    (fourTermLabels (by omega : 23 ≤ 23) ⟨19,j,x⟩).toFinset=keys (keyIndex 19 j x) := by decide +kernel
lemma cover_20 : ∀ j : Fin 10, ∀ x : Fin 2,
  (fourTermLabels (by omega : 23 ≤ 23) ⟨20,j,x⟩).Nodup →
    (fourTermLabels (by omega : 23 ≤ 23) ⟨20,j,x⟩).toFinset=keys (keyIndex 20 j x) := by decide +kernel
lemma cover_21 : ∀ j : Fin 11, ∀ x : Fin 2,
  (fourTermLabels (by omega : 23 ≤ 23) ⟨21,j,x⟩).Nodup →
    (fourTermLabels (by omega : 23 ≤ 23) ⟨21,j,x⟩).toFinset=keys (keyIndex 21 j x) := by decide +kernel
lemma cover_22 : ∀ j : Fin 11, ∀ x : Fin 1,
  (fourTermLabels (by omega : 23 ≤ 23) ⟨22,j,x⟩).Nodup →
    (fourTermLabels (by omega : 23 ≤ 23) ⟨22,j,x⟩).toFinset=keys (keyIndex 22 j x) := by decide +kernel
lemma cover_23 : ∀ j : Fin 12, ∀ x : Fin 1,
  (fourTermLabels (by omega : 23 ≤ 23) ⟨23,j,x⟩).Nodup →
    (fourTermLabels (by omega : 23 ≤ 23) ⟨23,j,x⟩).toFinset=keys (keyIndex 23 j x) := by decide +kernel
lemma cover : ∀ b : FourTerm 23, (fourTermLabels (by omega : 23 ≤ 23) b).Nodup →
    (fourTermLabels (by omega : 23 ≤ 23) b).toFinset=keys (keyIndex b.1 b.2.1 b.2.2) := by
  rintro ⟨n,j,x⟩
  fin_cases n
  · exact cover_0 j x
  · exact cover_1 j x
  · exact cover_2 j x
  · exact cover_3 j x
  · exact cover_4 j x
  · exact cover_5 j x
  · exact cover_6 j x
  · exact cover_7 j x
  · exact cover_8 j x
  · exact cover_9 j x
  · exact cover_10 j x
  · exact cover_11 j x
  · exact cover_12 j x
  · exact cover_13 j x
  · exact cover_14 j x
  · exact cover_15 j x
  · exact cover_16 j x
  · exact cover_17 j x
  · exact cover_18 j x
  · exact cover_19 j x
  · exact cover_20 j x
  · exact cover_21 j x
  · exact cover_22 j x
  · exact cover_23 j x
lemma representatives_checked : ∀ a : Fin 84,
  (fourTermLabels (by omega : 23 ≤ 23) (representatives a)).Nodup ∧
  (fourTermLabels (by omega : 23 ≤ 23) (representatives a)).toFinset=keys a := by decide +kernel
lemma keys_checked : fourKeys (by omega : 23 ≤ 23) = Finset.univ.image keys :=
  fourKeys_of_index (by omega : 23 ≤ 23) keys (fun b => keyIndex b.1 b.2.1 b.2.2)
    representatives cover representatives_checked
lemma keys_injective : Function.Injective keys := by decide +kernel
lemma keys_card : ∀ a : Fin 84, (keys a).card=4 := by decide +kernel
lemma fibers_cover : ∀ b : FourTerm 23,
    (fourTermLabels (by omega : 23 ≤ 23) b).Nodup →
      b ∈ fibers (keyIndex b.1 b.2.1 b.2.2) := by
  apply checkFourTerms_sound
  decide +kernel
lemma fibers_sound : ∀ a : Fin 84, ∀ b ∈ fibers a,
    (fourTermLabels (by omega : 23 ≤ 23) b).toFinset=keys a := by
  apply checkFourFibersSound_sound
  decide +kernel
lemma fibers_checked : ∀ a : Fin 84, ∀ b : FourTerm 23,
    (fourTermLabels (by omega : 23 ≤ 23) b).toFinset=keys a ↔ b ∈ fibers a :=
  fourFibers_of_index (by omega : 23 ≤ 23) keys
    (fun b => keyIndex b.1 b.2.1 b.2.2) fibers keys_injective keys_card cover fibers_cover fibers_sound
lemma columns_checked_0 : ∀ v : Fin 84, (∑ b ∈ fibers v, fourTermEval 23 (2*(0 : Fin 12).val+1) b * Occupation.wordSign (fourTermLabels (by omega : 23 ≤ 23) b)) = columns 0 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma columns_checked_1 : ∀ v : Fin 84, (∑ b ∈ fibers v, fourTermEval 23 (2*(1 : Fin 12).val+1) b * Occupation.wordSign (fourTermLabels (by omega : 23 ≤ 23) b)) = columns 1 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma columns_checked_2 : ∀ v : Fin 84, (∑ b ∈ fibers v, fourTermEval 23 (2*(2 : Fin 12).val+1) b * Occupation.wordSign (fourTermLabels (by omega : 23 ≤ 23) b)) = columns 2 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma columns_checked_3 : ∀ v : Fin 84, (∑ b ∈ fibers v, fourTermEval 23 (2*(3 : Fin 12).val+1) b * Occupation.wordSign (fourTermLabels (by omega : 23 ≤ 23) b)) = columns 3 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma columns_checked_4 : ∀ v : Fin 84, (∑ b ∈ fibers v, fourTermEval 23 (2*(4 : Fin 12).val+1) b * Occupation.wordSign (fourTermLabels (by omega : 23 ≤ 23) b)) = columns 4 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma columns_checked_5 : ∀ v : Fin 84, (∑ b ∈ fibers v, fourTermEval 23 (2*(5 : Fin 12).val+1) b * Occupation.wordSign (fourTermLabels (by omega : 23 ≤ 23) b)) = columns 5 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma columns_checked_6 : ∀ v : Fin 84, (∑ b ∈ fibers v, fourTermEval 23 (2*(6 : Fin 12).val+1) b * Occupation.wordSign (fourTermLabels (by omega : 23 ≤ 23) b)) = columns 6 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma columns_checked_7 : ∀ v : Fin 84, (∑ b ∈ fibers v, fourTermEval 23 (2*(7 : Fin 12).val+1) b * Occupation.wordSign (fourTermLabels (by omega : 23 ≤ 23) b)) = columns 7 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma columns_checked_8 : ∀ v : Fin 84, (∑ b ∈ fibers v, fourTermEval 23 (2*(8 : Fin 12).val+1) b * Occupation.wordSign (fourTermLabels (by omega : 23 ≤ 23) b)) = columns 8 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma columns_checked_9 : ∀ v : Fin 84, (∑ b ∈ fibers v, fourTermEval 23 (2*(9 : Fin 12).val+1) b * Occupation.wordSign (fourTermLabels (by omega : 23 ≤ 23) b)) = columns 9 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma columns_checked_10 : ∀ v : Fin 84, (∑ b ∈ fibers v, fourTermEval 23 (2*(10 : Fin 12).val+1) b * Occupation.wordSign (fourTermLabels (by omega : 23 ≤ 23) b)) = columns 10 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma columns_checked_11 : ∀ v : Fin 84, (∑ b ∈ fibers v, fourTermEval 23 (2*(11 : Fin 12).val+1) b * Occupation.wordSign (fourTermLabels (by omega : 23 ≤ 23) b)) = columns 11 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma columns_checked : ∀ u : Fin 12, ∀ v : Fin 84, (∑ b ∈ fibers v, fourTermEval 23 (2*u.val+1) b * Occupation.wordSign (fourTermLabels (by omega : 23 ≤ 23) b)) = columns u v := by
  intro u
  fin_cases u
  · exact columns_checked_0
  · exact columns_checked_1
  · exact columns_checked_2
  · exact columns_checked_3
  · exact columns_checked_4
  · exact columns_checked_5
  · exact columns_checked_6
  · exact columns_checked_7
  · exact columns_checked_8
  · exact columns_checked_9
  · exact columns_checked_10
  · exact columns_checked_11
lemma gram_checked_0 : ∀ v : Fin 12, (∑ a : Fin 84, columns (0 : Fin 12) a * columns v a / setFactorial (keys a)) = Z 0 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma gram_checked_1 : ∀ v : Fin 12, (∑ a : Fin 84, columns (1 : Fin 12) a * columns v a / setFactorial (keys a)) = Z 1 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma gram_checked_2 : ∀ v : Fin 12, (∑ a : Fin 84, columns (2 : Fin 12) a * columns v a / setFactorial (keys a)) = Z 2 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma gram_checked_3 : ∀ v : Fin 12, (∑ a : Fin 84, columns (3 : Fin 12) a * columns v a / setFactorial (keys a)) = Z 3 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma gram_checked_4 : ∀ v : Fin 12, (∑ a : Fin 84, columns (4 : Fin 12) a * columns v a / setFactorial (keys a)) = Z 4 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma gram_checked_5 : ∀ v : Fin 12, (∑ a : Fin 84, columns (5 : Fin 12) a * columns v a / setFactorial (keys a)) = Z 5 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma gram_checked_6 : ∀ v : Fin 12, (∑ a : Fin 84, columns (6 : Fin 12) a * columns v a / setFactorial (keys a)) = Z 6 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma gram_checked_7 : ∀ v : Fin 12, (∑ a : Fin 84, columns (7 : Fin 12) a * columns v a / setFactorial (keys a)) = Z 7 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma gram_checked_8 : ∀ v : Fin 12, (∑ a : Fin 84, columns (8 : Fin 12) a * columns v a / setFactorial (keys a)) = Z 8 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma gram_checked_9 : ∀ v : Fin 12, (∑ a : Fin 84, columns (9 : Fin 12) a * columns v a / setFactorial (keys a)) = Z 9 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma gram_checked_10 : ∀ v : Fin 12, (∑ a : Fin 84, columns (10 : Fin 12) a * columns v a / setFactorial (keys a)) = Z 10 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma gram_checked_11 : ∀ v : Fin 12, (∑ a : Fin 84, columns (11 : Fin 12) a * columns v a / setFactorial (keys a)) = Z 11 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma gram_checked : ∀ u : Fin 12, ∀ v : Fin 12, (∑ a : Fin 84, columns u a * columns v a / setFactorial (keys a)) = Z u v := by
  intro u
  fin_cases u
  · exact gram_checked_0
  · exact gram_checked_1
  · exact gram_checked_2
  · exact gram_checked_3
  · exact gram_checked_4
  · exact gram_checked_5
  · exact gram_checked_6
  · exact gram_checked_7
  · exact gram_checked_8
  · exact gram_checked_9
  · exact gram_checked_10
  · exact gram_checked_11
lemma rows_table_checked_0 : ∀ v : Fin 12, integerTableEval 23 SumTable23.sums (0 : Fin 12) v = Y 0 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma rows_table_checked_1 : ∀ v : Fin 12, integerTableEval 23 SumTable23.sums (1 : Fin 12) v = Y 1 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma rows_table_checked_2 : ∀ v : Fin 12, integerTableEval 23 SumTable23.sums (2 : Fin 12) v = Y 2 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma rows_table_checked_3 : ∀ v : Fin 12, integerTableEval 23 SumTable23.sums (3 : Fin 12) v = Y 3 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma rows_table_checked_4 : ∀ v : Fin 12, integerTableEval 23 SumTable23.sums (4 : Fin 12) v = Y 4 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma rows_table_checked_5 : ∀ v : Fin 12, integerTableEval 23 SumTable23.sums (5 : Fin 12) v = Y 5 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma rows_table_checked_6 : ∀ v : Fin 12, integerTableEval 23 SumTable23.sums (6 : Fin 12) v = Y 6 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma rows_table_checked_7 : ∀ v : Fin 12, integerTableEval 23 SumTable23.sums (7 : Fin 12) v = Y 7 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma rows_table_checked_8 : ∀ v : Fin 12, integerTableEval 23 SumTable23.sums (8 : Fin 12) v = Y 8 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma rows_table_checked_9 : ∀ v : Fin 12, integerTableEval 23 SumTable23.sums (9 : Fin 12) v = Y 9 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma rows_table_checked_10 : ∀ v : Fin 12, integerTableEval 23 SumTable23.sums (10 : Fin 12) v = Y 10 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma rows_table_checked_11 : ∀ v : Fin 12, integerTableEval 23 SumTable23.sums (11 : Fin 12) v = Y 11 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma rows_table_checked : ∀ u : Fin 12, ∀ v : Fin 12, integerTableEval 23 SumTable23.sums u v = Y u v := by
  intro u
  fin_cases u
  · exact rows_table_checked_0
  · exact rows_table_checked_1
  · exact rows_table_checked_2
  · exact rows_table_checked_3
  · exact rows_table_checked_4
  · exact rows_table_checked_5
  · exact rows_table_checked_6
  · exact rows_table_checked_7
  · exact rows_table_checked_8
  · exact rows_table_checked_9
  · exact rows_table_checked_10
  · exact rows_table_checked_11
lemma rows_checked (u v : Fin 12) : exactFourEval 23 (2*u.val+1) (2*v.val+1) = Y u v := by
  rw [exactFourEval_table 23 SumTable23.sums SumTable23.sums_checked]
  exact rows_table_checked u v
lemma product_checked_0 : ∀ v : Fin 12, (Z * tableComparison 23 (1/200000) Y) (0 : Fin 12) v = W 0 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma product_checked_1 : ∀ v : Fin 12, (Z * tableComparison 23 (1/200000) Y) (1 : Fin 12) v = W 1 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma product_checked_2 : ∀ v : Fin 12, (Z * tableComparison 23 (1/200000) Y) (2 : Fin 12) v = W 2 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma product_checked_3 : ∀ v : Fin 12, (Z * tableComparison 23 (1/200000) Y) (3 : Fin 12) v = W 3 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma product_checked_4 : ∀ v : Fin 12, (Z * tableComparison 23 (1/200000) Y) (4 : Fin 12) v = W 4 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma product_checked_5 : ∀ v : Fin 12, (Z * tableComparison 23 (1/200000) Y) (5 : Fin 12) v = W 5 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma product_checked_6 : ∀ v : Fin 12, (Z * tableComparison 23 (1/200000) Y) (6 : Fin 12) v = W 6 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma product_checked_7 : ∀ v : Fin 12, (Z * tableComparison 23 (1/200000) Y) (7 : Fin 12) v = W 7 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma product_checked_8 : ∀ v : Fin 12, (Z * tableComparison 23 (1/200000) Y) (8 : Fin 12) v = W 8 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma product_checked_9 : ∀ v : Fin 12, (Z * tableComparison 23 (1/200000) Y) (9 : Fin 12) v = W 9 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma product_checked_10 : ∀ v : Fin 12, (Z * tableComparison 23 (1/200000) Y) (10 : Fin 12) v = W 10 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma product_checked_11 : ∀ v : Fin 12, (Z * tableComparison 23 (1/200000) Y) (11 : Fin 12) v = W 11 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma product_checked : ∀ u : Fin 12, ∀ v : Fin 12, (Z * tableComparison 23 (1/200000) Y) u v = W u v := by
  intro u
  fin_cases u
  · exact product_checked_0
  · exact product_checked_1
  · exact product_checked_2
  · exact product_checked_3
  · exact product_checked_4
  · exact product_checked_5
  · exact product_checked_6
  · exact product_checked_7
  · exact product_checked_8
  · exact product_checked_9
  · exact product_checked_10
  · exact product_checked_11
lemma compression_checked_0 : ∀ v : Fin 12, (W * Z) (0 : Fin 12) v = M 0 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma compression_checked_1 : ∀ v : Fin 12, (W * Z) (1 : Fin 12) v = M 1 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma compression_checked_2 : ∀ v : Fin 12, (W * Z) (2 : Fin 12) v = M 2 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma compression_checked_3 : ∀ v : Fin 12, (W * Z) (3 : Fin 12) v = M 3 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma compression_checked_4 : ∀ v : Fin 12, (W * Z) (4 : Fin 12) v = M 4 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma compression_checked_5 : ∀ v : Fin 12, (W * Z) (5 : Fin 12) v = M 5 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma compression_checked_6 : ∀ v : Fin 12, (W * Z) (6 : Fin 12) v = M 6 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma compression_checked_7 : ∀ v : Fin 12, (W * Z) (7 : Fin 12) v = M 7 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma compression_checked_8 : ∀ v : Fin 12, (W * Z) (8 : Fin 12) v = M 8 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma compression_checked_9 : ∀ v : Fin 12, (W * Z) (9 : Fin 12) v = M 9 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma compression_checked_10 : ∀ v : Fin 12, (W * Z) (10 : Fin 12) v = M 10 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma compression_checked_11 : ∀ v : Fin 12, (W * Z) (11 : Fin 12) v = M 11 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma compression_checked : ∀ u : Fin 12, ∀ v : Fin 12, (W * Z) u v = M u v := by
  intro u
  fin_cases u
  · exact compression_checked_0
  · exact compression_checked_1
  · exact compression_checked_2
  · exact compression_checked_3
  · exact compression_checked_4
  · exact compression_checked_5
  · exact compression_checked_6
  · exact compression_checked_7
  · exact compression_checked_8
  · exact compression_checked_9
  · exact compression_checked_10
  · exact compression_checked_11
lemma ldl_checked_0 : ∀ v : Fin 12, (∑ k : Fin 12, L (0 : Fin 12) k * diag k * L v k) = M 0 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma ldl_checked_1 : ∀ v : Fin 12, (∑ k : Fin 12, L (1 : Fin 12) k * diag k * L v k) = M 1 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma ldl_checked_2 : ∀ v : Fin 12, (∑ k : Fin 12, L (2 : Fin 12) k * diag k * L v k) = M 2 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma ldl_checked_3 : ∀ v : Fin 12, (∑ k : Fin 12, L (3 : Fin 12) k * diag k * L v k) = M 3 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma ldl_checked_4 : ∀ v : Fin 12, (∑ k : Fin 12, L (4 : Fin 12) k * diag k * L v k) = M 4 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma ldl_checked_5 : ∀ v : Fin 12, (∑ k : Fin 12, L (5 : Fin 12) k * diag k * L v k) = M 5 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma ldl_checked_6 : ∀ v : Fin 12, (∑ k : Fin 12, L (6 : Fin 12) k * diag k * L v k) = M 6 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma ldl_checked_7 : ∀ v : Fin 12, (∑ k : Fin 12, L (7 : Fin 12) k * diag k * L v k) = M 7 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma ldl_checked_8 : ∀ v : Fin 12, (∑ k : Fin 12, L (8 : Fin 12) k * diag k * L v k) = M 8 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma ldl_checked_9 : ∀ v : Fin 12, (∑ k : Fin 12, L (9 : Fin 12) k * diag k * L v k) = M 9 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma ldl_checked_10 : ∀ v : Fin 12, (∑ k : Fin 12, L (10 : Fin 12) k * diag k * L v k) = M 10 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma ldl_checked_11 : ∀ v : Fin 12, (∑ k : Fin 12, L (11 : Fin 12) k * diag k * L v k) = M 11 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma ldl_checked : ∀ u : Fin 12, ∀ v : Fin 12, (∑ k : Fin 12, L u k * diag k * L v k) = M u v := by
  intro u
  fin_cases u
  · exact ldl_checked_0
  · exact ldl_checked_1
  · exact ldl_checked_2
  · exact ldl_checked_3
  · exact ldl_checked_4
  · exact ldl_checked_5
  · exact ldl_checked_6
  · exact ldl_checked_7
  · exact ldl_checked_8
  · exact ldl_checked_9
  · exact ldl_checked_10
  · exact ldl_checked_11
lemma diag_checked : ∀ u : Fin 12, 0 ≤ diag u := by decide +kernel
lemma certificate : FourCertificate (fun a : Fin 8 => (exactRows a).toReal) (1/200000) 23 (by omega) := by
  have hh := fourCertificate_of_tables exactRows (1/200000) (by omega : 23 ≤ 23) Y Z
  suffices FourCertificate (fun a : Fin 8 => (exactRows a).toReal) ((1/200000:ℚ):ℝ) 23 (by omega) by simpa using this
  apply hh
  · intro u v
    rw [exactFourEval_eq (by omega)]
    exact rows_checked u v
  · intro u v
    rw [rationalCreatedGram_of_columns (by omega : 23 ≤ 23) keys columns keys_checked keys_injective]
    · exact gram_checked u v
    · intro i a
      rw [fourColumn_eq_fiber (by omega : 23 ≤ 23) (2*i.val+1) (keys a) (fibers a) (fibers_checked a)]
      exact columns_checked i a
  · rw [Matrix.ext product_checked, Matrix.ext compression_checked]
    apply rational_ldl_positive M L diag diag_checked
    ext u v
    rw [Matrix.mul_apply]
    simpa only [Matrix.mul_diagonal,Matrix.transpose_apply] using (ldl_checked u v).symm
end Certificate23
end LaughlinGap.RealOccupation

end

end OAI
