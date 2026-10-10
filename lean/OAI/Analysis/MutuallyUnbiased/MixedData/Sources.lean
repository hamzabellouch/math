import OAI.Analysis.MutuallyUnbiased.MixedData.Source0
import OAI.Analysis.MutuallyUnbiased.MixedData.Source1
import OAI.Analysis.MutuallyUnbiased.MixedData.Source2
import OAI.Analysis.MutuallyUnbiased.MixedData.Source3
import OAI.Analysis.MutuallyUnbiased.MixedData.Source4
import OAI.Analysis.MutuallyUnbiased.MixedData.Source5
import OAI.Analysis.MutuallyUnbiased.MixedData.Source6
import OAI.Analysis.MutuallyUnbiased.MixedData.Source7
import OAI.Analysis.MutuallyUnbiased.MixedData.Source8
import OAI.Analysis.MutuallyUnbiased.MixedData.Source9
import OAI.Analysis.MutuallyUnbiased.MixedData.Source10
import OAI.Analysis.MutuallyUnbiased.MixedData.Source11
import OAI.Analysis.MutuallyUnbiased.MixedData.Source12
import OAI.Analysis.MutuallyUnbiased.MixedData.Source13
import OAI.Analysis.MutuallyUnbiased.MixedData.Source14
import OAI.Analysis.MutuallyUnbiased.MixedData.Source15
import OAI.Analysis.MutuallyUnbiased.MixedData.Source16
import OAI.Analysis.MutuallyUnbiased.MixedData.Source17
import OAI.Analysis.MutuallyUnbiased.MixedData.Source18

namespace OAI

namespace MUB6.Certificate.MixedData

def sourceRows (i : Fin 2425) : Integer.Sparse (Fin 3237) :=
  ((#[sourceChunk0, sourceChunk1, sourceChunk2, sourceChunk3, sourceChunk4, sourceChunk5, sourceChunk6, sourceChunk7, sourceChunk8, sourceChunk9, sourceChunk10, sourceChunk11, sourceChunk12, sourceChunk13, sourceChunk14, sourceChunk15, sourceChunk16, sourceChunk17, sourceChunk18])[i.val / 128]!)[i.val % 128]!

end MUB6.Certificate.MixedData

end OAI
